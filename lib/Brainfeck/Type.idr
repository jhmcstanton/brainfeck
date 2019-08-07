module Brainfeck.Type

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
