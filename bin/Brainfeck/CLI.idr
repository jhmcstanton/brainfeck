module Main

import Control.ST
import Data.Fuel
import System

import Brainfeck.ST

CharIO IO where
  getChar = lift getChar
  putChar = lift . putChar
  info    = lift . putStrLn

FilePath : Type
FilePath = String

usage : IO ()
usage =
  let lines = [
      ""
    , "Brainfeck: A somewhat well typed Brainfuck Interpreter."
    , ""
    , "Usage:"
    , "    brainfeck PATH/TO/BRAINFUCK/PROGRAM"
  ] in
  traverse putStrLn lines >>= \_ => pure ()

programFile : IO String
programFile = do
  args <- getArgs
  case inBounds 1 args of
    No contra => do putStrLn "Exactly 1 argument should be provided."
                    usage
                    exitFailure
    Yes prf   => pure (index 1 args)

export
main : IO ()
main = do
  programPath <- programFile
  Left e  <- readFile programPath | (Right prog) =>
                                      run (runProgram False False forever prog)
  putStrLn ("Error reading file: " ++ programPath)
  printLn e
