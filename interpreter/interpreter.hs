module Main where

import Analyzer
import Executor

import ParCascal
import AbsCascal

import Control.Monad.State
import Control.Monad.Error

import Data.Map

import System.Environment

main = do {
  args <- getArgs;
  case length (args) of
    0 -> putStrLn "File with program to run was not provided."

    1 -> do {
      input <- readFile (head (args));
      case parse pProgram input of
        Nothing -> putStrLn "Program could not be parsed.";

        Just program -> case staticAnalysis program of

          Left result -> do {
            putStrLn "Program was parsed. Static analysis finished with errors:";
            print result;
          }

          Right _ -> do {
            let Pr instructions = program in do {
              runStateT (executeInstrList instructions) ((empty, empty), empty);
              return ();
            }
          }
    }

    _ -> putStrLn "Too many arguments."

}
