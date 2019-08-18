module Brainfeck.Type

import Data.Vect

%default total

public export
Label : Nat -> Type
Label = Fin

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
data Operation : Nat -> Type where
  OLeft        : Operation n -- <
  ORight       : Operation n -- >
  OInc         : Operation n -- +
  ODec         : Operation n -- -
  OOut         : Operation n -- .
  OIn          : Operation n -- ,
  OJumpZero    : Label f -> Operation f-- [
  OJumpNZero   : Label b -> Operation b -- ]

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

export
operationToS : Operation f -> String
operationToS OLeft          = "<"
operationToS ORight         = ">"
operationToS OInc           = "+"
operationToS ODec           = "-"
operationToS OOut           = "."
operationToS OIn            = ","
operationToS (OJumpZero  l) = "[ " ++ show (finToNat l)
operationToS (OJumpNZero l) = show (finToNat l) ++ " ]"

public export
data Location : Type where
  Loc : (line : Nat) -> (col : Nat) -> Location

export
locToS : Location -> String
locToS (Loc l c) = "Line: " ++ show l ++ " Column: " ++ show c

public export
Tokens   : Nat -> Type
Tokens n = Vect n (Location, Token)
%name Tokens tokens

-- TODO: Use a better datatype for this (Brainfeck.Instructions.Instructions?)
-- This hasn't been profiled, but it seems trivially true that doing "random" access indexing
-- with ineffecient Fin's is going to cause speed problems
-- Probably wait until its actually an issue first though
public export
Instructions   : Nat -> Type
Instructions n = Vect n (Operation n)
%name Instructions instructions
