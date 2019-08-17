module Brainfeck.Lex

import Data.Vect as V

import Brainfeck.Type

%default total

token : Char -> Maybe Token
token '<' = Just TLeft
token '>' = Just TRight
token '+' = Just TInc
token '-' = Just TDec
token '.' = Just TOut
token ',' = Just TIn
token '[' = Just TJumpForward
token ']' = Just TJumpBack
token _   = Nothing


lexList : List Char -> (num_tokens : Nat ** Tokens num_tokens)
lexList [] = (0 ** V.Nil)
lexList (x :: xs) =
  case lexList xs of
    (_ ** tokens) => case token x of
                         Nothing => (_ ** tokens)
                         (Just t) => (_ ** t :: tokens)

export
lex : (program : String) -> (num_tokens ** Tokens num_tokens)
lex program = lexList (unpack program)
