module Executor where

import AbsCascal

import Control.Monad.State
import Control.Monad.Error

import Data.Map

import Text.Read (readMaybe)

data Variable = VInt Integer | VBool Bool | VString String
  deriving (Eq, Ord, Show, Read)

type VariablesStore = Map String Int
type VariablesState = Map Int Variable
type VariablesEnvironment = (VariablesStore, VariablesState)
type ProceduresEnvironment = Map String ([String], [Stm])
type ExecutionState = (VariablesEnvironment, ProceduresEnvironment)

executeInstrList :: [Instr] -> StateT ExecutionState IO ()
executeInstrList [] = return ()

executeInstrList (h:t) =
  case h of
    RegularI statement -> do {
      executeStm statement;
      executeInstrList t;
    }

    ProcDefI def -> do {
      executeProcDef def;
      executeInstrList t;
    }

executeStm :: Stm -> StateT ExecutionState IO ()
executeStm statement =
  case statement of
      PrintS printS -> executePrint printS

      ExprS exprS -> executeExpr exprS

      DeclS declS -> executeDecl declS

      AssignS assignS -> executeAssign assignS

      IfS ifS -> executeIf ifS

      LoopS loopS -> executeLoop loopS

      PrCallS prCallS -> executePrCall prCallS

executeStmList :: [Stm] -> StateT ExecutionState IO ()
executeStmList [] = return ()

executeStmList (h:t) = do {
  executeStm h;
  executeStmList t;
}

executeProcDef :: ProcDef -> StateT ExecutionState IO ()
executeProcDef def =
  let PrDef (Ident ident) arguments body = def in executePrDef ident arguments body

executePrDef :: String -> ArgsDef -> [Stm] -> StateT ExecutionState IO ()
executePrDef ident arguments body = do {
  let argumentsList = reverse (readProcArguments arguments) in
    let onlyIdentsList = Prelude.map (\(i, _) -> i) argumentsList in do {
      (varsEnv, procsEnv) <- get;
      put(varsEnv, insert ident (onlyIdentsList, body) procsEnv);
      return ();
    }
}

readProcArguments :: ArgsDef -> [(String, TypeSpecifier)]
readProcArguments prArguments =
  case prArguments of
    MultipleArgsDef argsDef typeSpecifier (Ident ident) -> 
      (ident, typeSpecifier):(readProcArguments argsDef)

    SingleArgDef typeSpecifier (Ident ident) ->
      [(ident, typeSpecifier)]

    NoArgsDef -> []

executeExpr :: Exp -> StateT ExecutionState IO ()
executeExpr exprS = do {
  (varsEnv, procsEnv) <- get;
  case calculateExpr exprS varsEnv of --force evaluation of expression, cascal is not a lazy language
    VInt intVal -> return ()
    VBool boolVal -> return ()
    VString stringVal -> return ()
}

executeDecl :: Decl -> StateT ExecutionState IO ()
executeDecl declS =
  let VarDecl typeSpecifier (Ident ident) expr = declS in do {
    (varsEnv, procsEnv) <- get;
    let val = calculateExpr expr varsEnv in
      let (varsStore, varsState) = varsEnv in 
        let newId = (size varsStore) + 1 in do {
          put((insert ident newId varsStore, insert newId val varsState), procsEnv);
          case val of --force evaluation of expression, cascal is not a lazy language
            VInt intVal -> return ()
            VBool boolVal -> return ()
            VString stringVal -> return ()
    }
  }

executeAssign :: Assign -> StateT ExecutionState IO ()
executeAssign assignS =
  let VarAssign (Ident ident) expr = assignS in do {
    (varsEnv, procsEnv) <- get;
    let val = calculateExpr expr varsEnv in 
      let (varsStore, varsState) = varsEnv in
        case (Data.Map.lookup ident varsStore) of
          Just i -> do {
            put((varsStore, insert i val varsState), procsEnv);
            case val of --force evaluation of expression, cascal is not a lazy language
              VInt intVal -> return ()
              VBool boolVal -> return ()
              VString stringVal -> return ()
          }

          Nothing -> error ("Variable not found " ++ show(ident));
  }

executeIf :: If -> StateT ExecutionState IO ()
executeIf ifS =
  case ifS of
    IfWithoutElse condition body -> do {
      (varsEnvBefore, procsEnvBefore) <- get;
      executeIfCondition condition body varsEnvBefore;
      (varsEnvAfter, _) <- get;
      let (varsStoreBefore, varsStateBefore) = varsEnvBefore in
        let (varsStoreAfter, varsStateAfter) = varsEnvAfter in do {
          put ((varsStoreBefore, intersection varsStateAfter varsStateBefore), procsEnvBefore);
          return ();
        }
    }

    IfWithElse condition ifBody elseBody -> do {
      (varsEnvBefore, procsEnvBefore) <- get;
      executeIfElseCondition condition ifBody elseBody varsEnvBefore;
      (varsEnvAfter, _) <- get;
      let (varsStoreBefore, varsStateBefore) = varsEnvBefore in
        let (varsStoreAfter, varsStateAfter) = varsEnvAfter in do {
          put ((varsStoreBefore, intersection varsStateAfter varsStateBefore), procsEnvBefore);
          return ();
        }
    }

executeIfCondition :: Exp -> [Stm] -> VariablesEnvironment -> StateT ExecutionState IO ()
executeIfCondition condition body varsEnv =
  case calculateExpr condition varsEnv of
    VBool True -> executeStmList body
    VBool False -> return ()

executeIfElseCondition :: Exp -> [Stm] -> [Stm] -> VariablesEnvironment -> StateT ExecutionState IO ()
executeIfElseCondition condition ifBody elseBody varsEnv =
  case calculateExpr condition varsEnv of
    VBool True -> executeStmList ifBody
    VBool False -> executeStmList elseBody

executeLoop :: Loop -> StateT ExecutionState IO ()
executeLoop loop =
  case loop of
    WhileLoop condition body -> do {
      (varsEnvBefore, procsEnvBefore) <- get;
      case calculateExpr condition varsEnvBefore of
        VBool True -> do {
          executeStmList body;
          (varsEnvAfter, _) <- get;
          let (varsStoreBefore, varsStateBefore) = varsEnvBefore in
            let (varsStoreAfter, varsStateAfter) = varsEnvAfter in do {
              put ((varsStoreBefore, intersection varsStateAfter varsStateBefore), procsEnvBefore);
              executeLoop loop;
            }
        }

        VBool False -> do {
          (varsEnvAfter, _) <- get;
          let (varsStoreBefore, varsStateBefore) = varsEnvBefore in
            let (varsStoreAfter, varsStateAfter) = varsEnvAfter in do {
              put ((varsStoreBefore, intersection varsStateAfter varsStateBefore), procsEnvBefore);
              return ();
            }
        }
    }

    ForLoop (ForAssignExp (Ident ident) initExpression) ForActionTo finalExpression body -> do {
      (varsEnvBefore, procsEnvBefore) <- get;
      case (calculateExpr initExpression varsEnvBefore, calculateExpr finalExpression varsEnvBefore) of
        (VInt initVal, VInt finalVal) -> do {
          if initVal > finalVal
            then error ("In 'for to' loop initial value was bigger than the final value.")
            else do {
              executeForAscending ident initVal finalVal body;
              (varsEnvAfter, _) <- get;
              let (varsStoreBefore, varsStateBefore) = varsEnvBefore in
                let (varsStoreAfter, varsStateAfter) = varsEnvAfter in do {
                  put ((varsStoreBefore, intersection varsStateAfter varsStateBefore), procsEnvBefore);
                  return ();
                }
            }
          }

        _ -> error ("For loop expected two ints.")
    }

    ForLoop (ForAssignExp (Ident ident) initExpression) ForActionDownto finalExpression body -> do {
      (varsEnvBefore, procsEnvBefore) <- get;
      case (calculateExpr initExpression varsEnvBefore, calculateExpr finalExpression varsEnvBefore) of
        (VInt initVal, VInt finalVal) -> do {
          if initVal < finalVal
            then error ("In 'for downto' loop initial value was smaller than the final value.")
            else do {
              executeForDescending ident initVal finalVal body;
              (varsEnvAfter, _) <- get;
              let (varsStoreBefore, varsStateBefore) = varsEnvBefore in
                let (varsStoreAfter, varsStateAfter) = varsEnvAfter in do {
                  put ((varsStoreBefore, intersection varsStateAfter varsStateBefore), procsEnvBefore);
                  return ();
                }
            }
        }

        _ -> error ("For loop expected two ints.")
    }

executeForAscending :: String -> Integer -> Integer -> [Stm] -> StateT ExecutionState IO ()
executeForAscending ident start end body =
  if start <= end
    then do {
      (varsEnv, procsEnv) <- get;
      let (varsStore, varsState) = varsEnv in
        let newId = (size varsStore) + 1 in
          let newVarsStore = (insert ident newId varsStore) in
            let newVarsState = (insert newId (VInt start) varsState) in do {
              put ((newVarsStore, newVarsState), procsEnv);
              executeStmList body;
              executeForAscending ident (start + 1) end body;
          }
    } 
    else return ();

executeForDescending :: String -> Integer -> Integer -> [Stm] -> StateT ExecutionState IO ()
executeForDescending ident start end body =
  if start >= end
    then do {
      (varsEnv, procsEnv) <- get;
      let (varsStore, varsState) = varsEnv in
        let newId = (size varsStore) + 1 in
          let newVarsStore = (insert ident newId varsStore) in
            let newVarsState = (insert newId (VInt start) varsState) in do {
              put ((newVarsStore, newVarsState), procsEnv);
              executeStmList body;
              executeForDescending ident (start - 1) end body;
            }
    }
    else return ();

executePrCall :: PrCall -> StateT ExecutionState IO ()
executePrCall callS =
  let ProcCall (Ident ident) arguments = callS in
    let argumentsList = reverse (readCallArguments arguments) in do {
      (varsEnvBefore, procsEnvBefore) <- get;
      case Data.Map.lookup ident procsEnvBefore of
        Just (argumentsNames, body) -> do {
          matchProcArguments ident argumentsList argumentsNames;
          executeStmList body;
          (varsEnvAfter, _) <- get;
          let (varsStoreBefore, varsStateBefore) = varsEnvBefore in
            let (varsStoreAfter, varsStateAfter) = varsEnvAfter in do {
              put ((varsStoreBefore, intersection varsStateAfter varsStateBefore), procsEnvBefore);
              return ();
            }
        }

        Nothing -> error ("Undeclared procedure " ++ show(ident));
    }

readCallArguments :: ArgsCall -> [Exp]
readCallArguments cArguments =
  case cArguments of
    ProcMultipleArgsCall argsCall expr -> 
      expr:(readCallArguments argsCall)

    ProcSingleArgCall expr -> [expr]

    ProcNoArgsCall -> []

matchProcArguments :: String -> [Exp] -> [String] -> StateT ExecutionState IO ()
matchProcArguments ident [] [] = return ()
matchProcArguments ident l [] = error ("Incorrect number of arguments for " ++ show(ident))
matchProcArguments ident [] l = error ("Incorrect number of arguments for " ++ show(ident))

matchProcArguments ident (eh:et) (nh:nt) = do {
  (varsEnv, procsEnv) <- get;
  let val = calculateExpr eh varsEnv in
    let (varsStore, varsState) = varsEnv in
      let newId = (size varsStore) + 1 in
        let newVarsStore = (insert nh newId varsStore) in
          let newVarsState = (insert newId val varsState) in do {
            put((newVarsStore, newVarsState), procsEnv);
            matchProcArguments ident et nt;
          }
}

executePrint :: PrintVal -> StateT ExecutionState IO ()
executePrint printS =
  let PrintInstr expr = printS in do {
    (varsEnv, _) <- get;
    case calculateExpr expr varsEnv of
      VInt intVal -> lift(putStrLn(show intVal))

      VString stringVal -> lift(putStrLn(show stringVal))

      VBool True -> lift(putStrLn("true"))

      VBool False -> lift(putStrLn("false"))
  }

calculateExpr :: Exp -> VariablesEnvironment -> Variable
calculateExpr expression varsEnv =
  case expression of
    EOr expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                    (VBool calVal1, VBool calVal2) -> VBool (calVal1 || calVal2)
                    _ -> error ("EOr expected two bools.")

    EAnd expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                     (VBool calVal1, VBool calVal2) -> VBool (calVal1 && calVal2)
                     _ -> error ("EAnd expected two bools.")

    EEqual expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                       (calExpr1, calExpr2) -> VBool (calExpr1 == calExpr2)

    ENotEqual expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                          (calExpr1, calExpr2) -> VBool (calExpr1 /= calExpr2)

    ELess expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                      (VInt calVal1, VInt calVal2) -> VBool (calVal1 < calVal2)
                      _ -> error ("ELess expected two ints.")

    EGreater expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                         (VInt calVal1, VInt calVal2) -> VBool (calVal1 > calVal2)
                         _ -> error ("EGreater expected two ints.")

    ELessOrEqual expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                             (VInt calVal1, VInt calVal2) -> VBool (calVal1 <= calVal2)
                             _ -> error ("ELessOrEqual expected two ints.")

    EGreaterOrEqual expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                                (VInt calVal1, VInt calVal2) -> VBool (calVal1 >= calVal2)
                                _ -> error ("EGreaterOrEqual exptected two ints.")

    EAdd expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                     (VInt calVal1, VInt calVal2) -> VInt (calVal1 + calVal2)
                     _ -> error ("EAdd expected two ints.")

    ESub expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                     (VInt calVal1, VInt calVal2) -> VInt (calVal1 - calVal2)
                     _ -> error ("ESub expected two ints.")

    EMul expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                     (VInt calVal1, VInt calVal2) -> VInt (calVal1 * calVal2)
                     _ -> error ("EMul exptected two ints.")

    EDiv expr1 expr2 -> case (calculateExpr expr1 varsEnv, calculateExpr expr2 varsEnv) of
                     (VInt calVal1, VInt 0) -> error ("Dividing by zero.")
                     (VInt calVal1, VInt calVal2) -> VInt (calVal1 `div` calVal2)
                     _ -> error ("EDiv expected two ints.")

    EVar (Ident ident) -> let (varsStore, varsState) = varsEnv in
                            case Data.Map.lookup ident varsStore of
                              Nothing -> error ("Undeclared variable " ++ show(ident))
                              Just i -> case Data.Map.lookup i varsState of
                                Nothing -> error ("Undeclared variable " ++ show(ident))
                                Just val -> val

    EInt intVal -> VInt (intVal)

    EString stringVal -> VString (stringVal)

    EBool BoolTrue -> VBool (True)

    EBool BoolFalse -> VBool (False)

    ECast (IntToString expr) -> case calculateExpr expr varsEnv of
                                  VInt calVal -> VString (show calVal)
                                  _ -> error ("IntToString expected int.")

    ECast (StringToInt expr) -> case calculateExpr expr varsEnv of
                                  VString calVal -> case readMaybeInteger calVal of
                                                      Just intVal -> VInt (intVal)
                                                      _ -> error ("Could not cast string to int.")
                                  _ -> error ("StringToInt expected string.")

readMaybeInteger :: String -> Maybe Integer
readMaybeInteger input = readMaybe input
