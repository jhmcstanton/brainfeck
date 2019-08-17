module Brainfeck.Type

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

public export
Label : Nat -> Type
Label = Fin

public export
data Operation : Type where
  OLeft        : Operation -- <
  ORight       : Operation -- >
  OInc         : Operation -- +
  ODec         : Operation -- -
  OOut         : Operation -- .
  OIn          : Operation -- ,
  OJumpForward : Label f -> Operation -- [
  OJumpBack    : Label b -> Operation -- ]

export
tokenToS : Token -> String
tokenToS TLeft = "<"
tokenToS TRight = ">"
tokenToS TInc = "+"
tokenToS TDec = "-"
tokenToS TOut = "."
tokenToS TIn = ","
tokenToS TJumpForward = "["
tokenToS TJumpBack = "]"

operationToS : Operation -> String
operationToS OLeft = "<"
operationToS ORight = ">"
operationToS OInc = "+"
operationToS ODec = "-"
operationToS OOut = "."
operationToS OIn = ","
operationToS (OJumpForward l) = "[ " ++ show (finToNat l)
operationToS (OJumpBack    l) = show (finToNat l) ++ " ]"

public export
Tokens   : Nat -> Type
Tokens n = Vect n Token
%name Tokens tokens

-- TODO: Use a better datatype for this (Brainfeck.Instructions.Instructions?)
-- This hasn't been profiled, but it seems trivially true that doing "random" access indexing
-- with ineffecient Fin's is going to cause speed problems
-- Probably wait until its actually an issue first though
public export
Instructions   : Nat -> Type
Instructions n = Vect n Token -- Operation
%name Instructions instructions
