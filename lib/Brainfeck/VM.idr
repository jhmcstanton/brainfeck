module Brainfeck.VM

import Data.Fin
import Data.Vect as V
import Prelude.List as L

import Brainfeck.Type

%default total

Cell : Type
Cell = Int

Instructions   : Nat -> Type
Instructions n = Vect n Token
%name Instructions instructions

Label : Nat -> Type
Label = Fin

record JumpLabels (instructionCount : Nat) where
  constructor Jumps
  back   : List (Fin instructionCount)
  foward : List (Fin instructionCount)
%name JumpLabels jumps

data Tape : (left : Nat) -> (right : Nat) -> (size : Nat) -> Type where
  MkTape : Vect left Cell
         -> Cell
         -> Vect right Cell
         -> Tape left right (left + right)
%name Tape tape

initTape : (size : Nat) -> Tape 0 size size
initTape size = MkTape V.Nil 0 (V.replicate size 0)

shiftLeft : Tape (S l) r (S (l + r)) -> Tape l (S r) (S (l + r))
shiftLeft {l} {r} (MkTape (x :: xs) c ys) = tape'
  where
    tape' = rewrite plusSuccRightSucc l r in MkTape xs x (c :: ys)

shiftRight : Tape l (S r) (l + (S r)) -> Tape (S l) r ((S l) + r)
shiftRight {l} {r} (MkTape xs c (y :: ys)) = tape'
  where
    tape' = MkTape (c :: xs) y ys

export
record VMState (cellCount : Nat) (instructionCount : Nat) where
  constructor    VM
  tapeIndex    : Fin cellCount
  pc           : Fin instructionCount
  cells        : Vect cellCount Cell
  instructions : Instructions instructionCount
%name VMState vm

InitialVMSize : Nat
InitialVMSize = 1000

-- it would be nice to use * instead of +
-- but that is trickier to work with.
-- These are linked lists anyway so eh
-- TODO: try using *
ExtendedSize   : Nat -> Nat
ExtendedSize n = n + n

initVM : Instructions (S n) -> VMState InitialVMSize (S n)
initVM instructions = VM 0 0 (replicate _ 0) instructions

extend : (idElem : a) -> Vect n a -> Vect (n + k) a
extend idElem [] = replicate _ idElem
extend idElem (y :: xs) = y :: extend idElem xs

growVM : VMState cellCount is -> VMState (ExtendedSize cellCount) is
growVM {cellCount} vm =
  VM tapeIndex' (pc vm) extendedCells (instructions vm)
  where
    extendedCells = extend 0 (cells vm)
    tapeIndex'    : Fin (ExtendedSize cellCount)
    tapeIndex'    = weakenN _ (tapeIndex vm)

-- collectJumps : Instructions (S n) -> JumpLabels (S n)
-- collectJumps is = collect 0 is where
--   collect : (Fin n) -> Instructions k -> JumpLabels k
--   collect _ [] = Jumps [] []
--   collect c (x :: xs) =
--     let (Jumps bs fs) = collect (weaken c) xs
--         counter       = finToNat c
--     in
--     case x of
--       TJumpForward => ?rhs_8
--       TJumpBack => ?rhs_9
--       _ => Jumps bs fs
