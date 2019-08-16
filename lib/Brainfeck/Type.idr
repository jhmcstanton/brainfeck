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


-- TODO: Use a better datatype for this (Brainfeck.Instructions.Instructions?)
-- This hasn't been profiled, but it seems trivially true that doing "random" access indexing
-- with ineffecient Fin's is going to cause speed problems
-- Probably wait until its actually an issue first though
public export
Instructions   : Nat -> Type
Instructions n = Vect n Token
%name Instructions instructions
