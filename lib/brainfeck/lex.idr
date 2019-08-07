module Brainfeck.Lex

import Data.Vect

%default total

public export
data Token     : Type  where
  TLeft        : Token -- <
  TRight       : Token -- >
  TInc         : Token -- +
  TDec         : Token -- -
  TOut         : Token -- .
  TIn          : Token -- ,
  TJumpForward : Token -- [
  TJumpBack    : Token -- ]

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


lexList : List Char -> (num_tokens : Nat ** Vect num_tokens Token)
lexList [] = (0 ** [])
lexList (x :: xs) =
  case lexList xs of
    (_ ** tokens) => case token x of
                         Nothing => (_ ** tokens)
                         (Just t) => (_ ** t :: tokens)

export
lex : (program : String) -> (num_tokens ** Vect num_tokens Token)
lex program = lexList (unpack program)
