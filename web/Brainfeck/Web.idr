module Main

import Control.ST
import Data.String.Extra

import Brainfeck.ST

jscall : (fname : String) -> (ty : Type)
       -> {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty

programId : String
programId = "program-text"

consoleId : String
consoleId = "console"

runButtonId : String
runButtonId = "run-button"

clearButtonId : String
clearButtonId = "clear"

programsListId : String
programsListId = "programs-list"

loadProgramButtonId : String
loadProgramButtonId = "load-program"

getLastChar : JS_IO Char
getLastChar = do
  text <- foreign FFI_JS "prompt(%0)"
                 (String -> JS_IO String)
                 "Enter a character:"
  case length text of
    Z     => pure ' ' -- user input the empty string
    (S n) => case index n text of
               Nothing => pure ' ' -- not possible
               Just c  => pure c

putConsoleString : String -> JS_IO ()
putConsoleString s =
  jscall "document.getElementById(%0).value += %1"
         (String -> String -> JS_IO ())
         consoleId s

putConsoleChar : Char -> JS_IO ()
putConsoleChar c = putConsoleString (singleton c)

CharIO JS_IO where
  getChar = lift getLastChar
  putChar = lift . putConsoleChar
  info    = lift . putConsoleString

runProgram : () -> JS_IO ()
runProgram _ = do
  program <- jscall "document.getElementById(%0).value"
                    (String -> JS_IO String)
                    programId
  run (runProgram False False program)

clear : () -> JS_IO ()
clear _ = do
  jscall "document.getElementById(%0).value = ''"
         (String -> JS_IO ())
         consoleId

rawGithubUrl : String -> String
rawGithubUrl s =
  "https://raw.githubusercontent.com/jhmcstanton/brainfeck/master/examples/"
    ++ s

load : () -> JS_IO ()
load _ = do
  index <- jscall "document.getElementById(%0).selectedIndex"
           (String -> JS_IO Int) programsListId
  programName <- jscall "document.getElementById(%0).options[%1].value"
                 (String -> Int -> JS_IO String)
           programsListId index
  jscall """
     fetch(%0).then(resp => resp.text().then(
         t => document.getElementById(%1).value = t))"""
         (String -> String -> JS_IO ()) (rawGithubUrl programName) programId

addButtonListener : (id : String) -> (() -> JS_IO ()) -> JS_IO ()
addButtonListener id f = do
  jscall "document.getElementById(%0).addEventListener('click', %1, false)"
         (String -> (JsFn (() -> JS_IO ())) -> JS_IO ())
         id (MkJsFn f)

main : JS_IO ()
main = do
  addButtonListener clearButtonId clear
  addButtonListener runButtonId runProgram
  addButtonListener loadProgramButtonId load
