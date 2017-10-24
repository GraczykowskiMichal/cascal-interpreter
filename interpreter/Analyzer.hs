module Analyzer where

import LexCascal
import ParCascal
import SkelCascal
import PrintCascal
import AbsCascal

import ErrM

import Control.Monad.State
import Control.Monad.Error

import Data.Map
import Data.List

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int

parse :: (Print a, Show a) => ParseFun a -> String -> Maybe a
parse p s = let ts = myLLexer s in case p ts of
           Bad s    -> Nothing
           Ok  tree -> Just tree

data AnalysisError = UndeclaredVariable String
                   | VariableRedeclaration String
                   | UndefinedProcedure String
                   | ProcedureRedefinition String
                   | ProcedureRepeatingArguments String
                   | IncorrectExpressionType Exp
                   | IncorrectProcedureCallArguments ArgsCall
                   | VerboseError String
                   deriving (Eq, Ord, Show)

instance Error AnalysisError where
    noMsg  = VerboseError "Error while performing static analysis"
    strMsg = VerboseError

type VariablesStore = Map String Int
type VariablesState = Map Int TypeSpecifier
type VariablesEnvironment = (VariablesStore, VariablesState)
type ProceduresEnvironment = Map String [(String, TypeSpecifier)]
type AnalysisState = (VariablesEnvironment, ProceduresEnvironment)

analyzeInstrList :: [Instr] -> ErrorT AnalysisError (State AnalysisState) ()
analyzeInstrList [] = return ()

analyzeInstrList (h:t) =
  case h of
    RegularI statement -> do {
      analyzeStm statement;
      analyzeInstrList t;
    }

    ProcDefI procDef -> do {
      analyzeProcDef procDef;
      analyzeInstrList t;
    }

analyzeStm :: Stm -> ErrorT AnalysisError (State AnalysisState) ()
analyzeStm statement =
  case statement of
    ExprS exprS -> analyzeExpr exprS

    DeclS declS -> analyzeDecl declS

    AssignS assignS -> analyzeAssign assignS

    IfS ifS -> analyzeIf ifS

    LoopS loopS -> analyzeLoop loopS

    PrCallS prCallS -> analyzePrCall prCallS

    PrintS printS -> analyzePrint printS

analyzeStmList :: [Stm] -> ErrorT AnalysisError (State AnalysisState) ()
analyzeStmList [] = return ()

analyzeStmList (h:t) = do {
  analyzeStm h;
  analyzeStmList t;
}

analyzeProcDef :: ProcDef -> ErrorT AnalysisError (State AnalysisState) ()
analyzeProcDef def =
  case def of
    PrDef identifier arguments body -> do {
      (varsEnvBefore, _) <- get;
      analyzePrDef identifier arguments;
      (_, procsEnvAfter) <- get;
      analyzeStmList body;
      put(varsEnvBefore, procsEnvAfter);
      return ();
    }

analyzePrDef :: Ident -> ArgsDef -> ErrorT AnalysisError (State AnalysisState) ()
analyzePrDef identifier arguments = do {
  let Ident ident = identifier in
    let argumentsList = readArguments arguments in
      let onlyIdentsList = Prelude.map (\(i, _) -> i) argumentsList in do {
        (varsEnv, procsEnv) <- get;
        let (varsStore, varsState) = varsEnv in do {
          if member ident procsEnv then throwError (ProcedureRedefinition ident) else get;
          if isUnique onlyIdentsList then get else throwError (ProcedureRepeatingArguments ident);
          let (argsVarsStore, argsVarsState) = storeAndStateFromArgsList (size varsStore) argumentsList in
            let newVarsStore = Data.Map.union argsVarsStore varsStore in
              let newVarsState = Data.Map.union varsState argsVarsState in do {
                put((newVarsStore, newVarsState), Data.Map.insert ident argumentsList procsEnv);
                return ();
              }
        }
      }
  }

storeAndStateFromArgsList :: Int -> [(String, TypeSpecifier)] -> (VariablesStore, VariablesState)
storeAndStateFromArgsList lastId argsList =
  storeAndStateFromArgsListHelp lastId argsList empty empty

storeAndStateFromArgsListHelp :: Int -> [(String, TypeSpecifier)] -> VariablesStore -> VariablesState -> (VariablesStore, VariablesState)
storeAndStateFromArgsListHelp _ [] storeAcc stateAcc = (storeAcc, stateAcc)

storeAndStateFromArgsListHelp lastId ((ident, typeSpecifier):t) storeAcc stateAcc =
  let newStoreAcc = Data.Map.insert ident (lastId + 1) storeAcc in
    let newStateAcc = Data.Map.insert (lastId + 1) typeSpecifier stateAcc in
      storeAndStateFromArgsListHelp (lastId + 1) t newStoreAcc newStateAcc

readArguments :: ArgsDef -> [(String, TypeSpecifier)]
readArguments arguments =
  case arguments of
    MultipleArgsDef argsDef typeSpecifier (Ident ident) -> 
      (ident, typeSpecifier):(readArguments argsDef)

    SingleArgDef typeSpecifier (Ident ident) ->
      [(ident, typeSpecifier)]

    NoArgsDef -> []

isUnique :: (Eq a) => [a] -> Bool
isUnique l = (length(nub(l)) == length(l))

analyzeExpr :: Exp -> ErrorT AnalysisError (State AnalysisState) ()
analyzeExpr exprS = do {
  validateExpr exprS;
  (varsEnv, _) <- get;
  let mTInt = matchesType exprS TInt varsEnv in
    let mTBool = matchesType exprS TBool varsEnv in
      let mTString = matchesType exprS TString varsEnv in
        case (mTInt, mTBool, mTString) of
          (False, False, False) -> throwError (IncorrectExpressionType exprS)
          _ -> return ();
}

analyzeDecl :: Decl -> ErrorT AnalysisError (State AnalysisState) ()
analyzeDecl declS =
  let VarDecl typeSpecifier (Ident ident) expr = declS in do {
    validateExpr expr;
    (varsEnv, procsEnv) <- get;
    if matchesType expr typeSpecifier varsEnv
      then return (); 
      else throwError (IncorrectExpressionType expr);
    let (varsStore, varsState) = varsEnv in do
      let newId = (size varsStore) + 1 in 
        let newVarsStore = Data.Map.insert ident newId varsStore in
          let newVarsState = Data.Map.insert newId typeSpecifier varsState in do {
            put((newVarsStore, newVarsState), procsEnv);
            return ();
          }
  }

analyzeAssign :: Assign -> ErrorT AnalysisError (State AnalysisState) ()
analyzeAssign assignS =
  let VarAssign (Ident ident) expr = assignS in do {
    validateExpr expr;
    (varsEnv, procsEnv) <- get;
    let (varsStore, varsState) = varsEnv in
      case Data.Map.lookup ident varsStore of
        Just i -> case Data.Map.lookup i varsState of
                    Just t -> if matchesType expr t varsEnv
                                then return (); 
                                else throwError (IncorrectExpressionType expr)
                    Nothing -> throwError (UndeclaredVariable ident);
        Nothing -> throwError (UndeclaredVariable ident);
  }

analyzeIf :: If -> ErrorT AnalysisError (State AnalysisState) ()
analyzeIf ifS =
  case ifS of
    IfWithoutElse condition body -> do {
      validateExpr condition;
      (varsEnvBefore, procsEnvBefore) <- get;
      if matchesType condition TBool varsEnvBefore 
        then get;
        else throwError (IncorrectExpressionType condition);
      analyzeStmList body;
      put(varsEnvBefore, procsEnvBefore);
      return ();
    }

    IfWithElse condition ifBody elseBody -> do {
      validateExpr condition;
      (varsEnvBefore, procsEnvBefore) <- get;
      if matchesType condition TBool varsEnvBefore
        then get;
        else throwError (IncorrectExpressionType condition);
      analyzeStmList ifBody;
      put(varsEnvBefore, procsEnvBefore);
      analyzeStmList elseBody;
      put(varsEnvBefore, procsEnvBefore);
      return ();
    }

analyzeLoop :: Loop -> ErrorT AnalysisError (State AnalysisState) ()
analyzeLoop loop =
  case loop of
    WhileLoop condition body -> do {
      validateExpr condition;
      (varsEnvBefore, procsEnvBefore) <- get;

      if matchesType condition TBool varsEnvBefore
        then get;
        else throwError (IncorrectExpressionType condition);

      analyzeStmList body;
      put(varsEnvBefore, procsEnvBefore);
      return ();
    }

    ForLoop (ForAssignExp (Ident ident) initExpression) forAction finalExpression body -> do {
      validateExpr initExpression;
      validateExpr finalExpression;
      (varsEnvBefore, procsEnvBefore) <- get;

      if matchesType initExpression TInt varsEnvBefore
        then get;
        else throwError (IncorrectExpressionType initExpression);

      if matchesType finalExpression TInt varsEnvBefore
        then get;
        else throwError (IncorrectExpressionType finalExpression);

      let (varsStoreBefore, varsStateBefore) = varsEnvBefore in
        let newId = (size varsStoreBefore) + 1 in
          let newVarsStore = Data.Map.insert ident newId varsStoreBefore in
            let newVarsState = Data.Map.insert newId TInt varsStateBefore in
              put ((newVarsStore, newVarsState), procsEnvBefore);

      analyzeStmList body;
      put(varsEnvBefore, procsEnvBefore);
      return ();
    }

analyzePrCall :: PrCall -> ErrorT AnalysisError (State AnalysisState) ()
analyzePrCall callS =
  let ProcCall (Ident ident) arguments = callS in
    let argumentsList = readCallArguments arguments in do {
      validateExprList argumentsList;
      (varsEnv, procsEnv) <- get;
      case Data.Map.lookup ident procsEnv of
        Just argsFromEnv -> let onlyTypesFromEnv = Data.List.map (\(_, t) -> t) argsFromEnv in
          if expsMatchTypes argumentsList onlyTypesFromEnv varsEnv
            then return ()
            else throwError (IncorrectProcedureCallArguments arguments);

        Nothing -> throwError (UndefinedProcedure ident);
    }

readCallArguments :: ArgsCall -> [Exp]
readCallArguments cArguments =
  case cArguments of
    ProcMultipleArgsCall argsCall expr -> 
      expr:(readCallArguments argsCall)

    ProcSingleArgCall expr -> [expr]

    ProcNoArgsCall -> []

expsMatchTypes :: [Exp] -> [TypeSpecifier] -> VariablesEnvironment -> Bool
expsMatchTypes [] [] _ = True
expsMatchTypes [] l _ = False
expsMatchTypes l [] _ = False

expsMatchTypes (eh:et) (th:tt) varsEnv =
  matchesType eh th varsEnv
  && expsMatchTypes et tt varsEnv

analyzePrint :: PrintVal -> ErrorT AnalysisError (State AnalysisState) ()
analyzePrint printS =
  let PrintInstr expr = printS in do {
    validateExpr expr;
    (varsEnv, _) <- get;
    let mTInt = matchesType expr TInt varsEnv in
     let mTBool = matchesType expr TBool varsEnv in
       let mTString = matchesType expr TString varsEnv in
         case (mTInt, mTBool, mTString) of
           (False, False, False) -> throwError (IncorrectExpressionType expr)
           _ -> return ();
  }
    
validateExprList :: [Exp] -> ErrorT AnalysisError (State AnalysisState) ()
validateExprList [] = return ()

validateExprList (h:t) = do {
  validateExpr h;
  validateExprList t;
}

validateExpr :: Exp -> ErrorT AnalysisError (State AnalysisState) ()
validateExpr expression =
  case expression of
    EOr expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    EAnd expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    EEqual expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    ENotEqual expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    ELess expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    EGreater expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    ELessOrEqual expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    EGreaterOrEqual expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    EAdd expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    ESub expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    EMul expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    EDiv expr1 expr2 -> do {
      validateExpr expr1;
      validateExpr expr2;
    }

    EVar (Ident ident) -> do {
      ((varsStore, _), _) <- get;
      if member ident varsStore then return (); else throwError (UndeclaredVariable ident);
    }

    ECast (IntToString expr) -> do {
      validateExpr expr;
    }

    ECast (StringToInt expr) -> do {
      validateExpr expr;
    }

    _ -> return ();

matchesType :: Exp -> TypeSpecifier -> VariablesEnvironment -> Bool
matchesType expression typeSpecifier varsEnv =
  case expression of
    EOr expr1 expr2 -> typeSpecifier == TBool
                       && matchesType expr1 TBool varsEnv
                       && matchesType expr2 TBool varsEnv

    EAnd expr1 expr2 -> typeSpecifier == TBool
                        && matchesType expr1 TBool varsEnv
                        && matchesType expr2 TBool varsEnv

    EEqual expr1 expr2 -> let type1 = expectedExprType expr1 varsEnv in
                            let type2 = expectedExprType expr2 varsEnv in
                              case (type1, type2) of
                                (Just t1, Just t2) -> typeSpecifier == TBool
                                                      && t1 == t2
                                                      && matchesType expr1 t1 varsEnv
                                                      && matchesType expr2 t2 varsEnv

                                _ -> False
                     
    ENotEqual expr1 expr2 -> let type1 = expectedExprType expr1 varsEnv in
                              let type2 = expectedExprType expr2 varsEnv in
                                case (type1, type2) of
                                  (Just t1, Just t2) -> typeSpecifier == TBool
                                                        && t1 == t2
                                                        && matchesType expr1 t1 varsEnv
                                                        && matchesType expr2 t2 varsEnv
                                  _ -> False

    ELess expr1 expr2 -> typeSpecifier == TBool
                         && matchesType expr1 TInt varsEnv
                         && matchesType expr2 TInt varsEnv

    EGreater expr1 expr2 -> typeSpecifier == TBool
                            && matchesType expr1 TInt varsEnv
                            && matchesType expr2 TInt varsEnv

    ELessOrEqual expr1 expr2 -> typeSpecifier == TBool
                                && matchesType expr1 TInt varsEnv
                                && matchesType expr2 TInt varsEnv

    EGreaterOrEqual expr1 expr2 -> typeSpecifier == TBool
                                   && matchesType expr1 TInt varsEnv
                                   && matchesType expr2 TInt varsEnv

    EAdd expr1 expr2 -> typeSpecifier == TInt
                        && matchesType expr1 TInt varsEnv
                        && matchesType expr2 TInt varsEnv

    ESub expr1 expr2 -> typeSpecifier == TInt
                        && matchesType expr1 TInt varsEnv
                        && matchesType expr2 TInt varsEnv

    EMul expr1 expr2 -> typeSpecifier == TInt
                        && matchesType expr1 TInt varsEnv
                        && matchesType expr2 TInt varsEnv

    EDiv expr1 expr2 -> typeSpecifier == TInt
                        && matchesType expr1 TInt varsEnv
                        && matchesType expr2 TInt varsEnv

    EVar (Ident ident) -> let (varsStore, varsState) = varsEnv in
                            case (Data.Map.lookup ident varsStore) of
                              Just i -> case (Data.Map.lookup i varsState) of
                                          Just t -> typeSpecifier == t
                                          Nothing -> False
                              Nothing -> False

    EInt _ -> typeSpecifier == TInt

    EString _ -> typeSpecifier == TString

    EBool _ -> typeSpecifier == TBool

    ECast (IntToString expr) -> typeSpecifier == TString
                                && matchesType expr TInt varsEnv

    ECast (StringToInt expr) -> typeSpecifier == TInt
                                && matchesType expr TString varsEnv

expectedExprType :: Exp -> VariablesEnvironment -> Maybe TypeSpecifier
expectedExprType expression varsEnv =
  case expression of
    EOr _ _ -> Just TBool

    EAnd _ _ -> Just TBool

    EEqual _ _ -> Just TBool

    ENotEqual _ _ -> Just TBool

    ELess _ _ -> Just TBool

    EGreater _ _ -> Just TBool

    ELessOrEqual _ _ -> Just TBool

    EGreaterOrEqual _ _ -> Just TBool

    EAdd _ _ -> Just TInt

    ESub _ _ -> Just TInt

    EMul _ _ -> Just TInt

    EDiv _ _ -> Just TInt

    EVar (Ident ident) -> let (varsStore, varsState) = varsEnv in
                            case (Data.Map.lookup ident varsStore) of
                              Just i -> Data.Map.lookup i varsState
                              Nothing -> Nothing

    EInt _ -> Just TInt

    EString _ -> Just TString

    EBool _ -> Just TBool

    ECast (IntToString _) -> Just TString

    ECast (StringToInt _) -> Just TInt

staticAnalysis :: Program -> Either AnalysisError ()
staticAnalysis program =
  let Pr instructions = program in
    evalState(runErrorT(analyzeInstrList instructions)) ((empty, empty), empty)
