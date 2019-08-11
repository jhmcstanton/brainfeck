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
  forward : List (Fin instructionCount)
%name JumpLabels jumps

collectJumps : Instructions (S n) -> JumpLabels (S n)
collectJumps {n} is = collect 0 is where
  collect : Integer -> Instructions k -> JumpLabels (S n)
  collect _ []        = Jumps [] []
  collect idx (x :: xs) =
    let jumps@(Jumps bs fs) = collect (idx + 1) xs in
    case x of
      TJumpForward => Jumps bs (restrict n idx :: fs)
      TJumpBack    => Jumps (restrict n idx :: bs) fs
      _            => jumps

data Tape : (left : Nat) -> (right : Nat) -> (size : Nat) -> Type where
  MkTape : Vect left Cell
         -> Cell
         -> Vect right Cell
         -> Tape left right (left + right)
%name Tape tape

namespace Tape
  left : Tape left right size -> Vect left Cell
  left (MkTape xs _ _) = xs

  leftLength : Tape left right size -> Nat
  leftLength (MkTape xs _ _) = length xs

  right : Tape left right size -> Vect right Cell
  right (MkTape _ _ ys) = ys

  rightLength : Tape left right size -> Nat
  rightLength (MkTape _ _ ys) = length ys

  length : Tape left right size -> Nat
  length tape = leftLength tape + rightLength tape

  current : Tape left right size -> Cell
  current (MkTape _ c _) = c

initTape : (size : Nat) -> Tape 0 size size
initTape size = MkTape V.Nil 0 (V.replicate size 0)

shiftLeft : Tape (S l) r (S (l + r)) -> Tape l (S r) (S (l + r))
shiftLeft {l} {r} (MkTape (x :: xs) c ys) = tape'
  where
    tape' = rewrite plusSuccRightSucc l r in MkTape xs x (c :: ys)

shiftRight : Tape l (S r) (l + (S r)) -> Tape (S l) r (S (l + r))
shiftRight {l} {r} (MkTape xs c (y :: ys)) = tape'
  where
    tape' = MkTape (c :: xs) y ys

extend : Tape left right (left + right) -> Tape left (right + k) (left + (right + k))
extend {left} {right} {k} (MkTape xs c ys) = tape' where
  tape' = MkTape xs c (extendVect ys)
  extendVect : Vect n Cell -> Vect (n + k) Cell
  extendVect [] = replicate _ 0
  extendVect (x :: xs) = x :: extendVect xs

export
record VMState (tapeLeft : Nat) (tapeRight : Nat) (instructionCount : Nat) where
  constructor    VM
  pc           : Fin instructionCount
  instructions : Instructions instructionCount
  cells        : Tape tapeLeft tapeRight (tapeLeft + tapeRight)
%name VMState vm

InitialVMSize : Nat
InitialVMSize = 1000

-- it would be nice to use * instead of +
-- but that is trickier to work with.
-- These are linked lists anyway so eh
-- TODO: try using *
ExtendedSize   : Nat -> Nat
ExtendedSize n = n + n

initVM : Instructions (S n) -> VMState 0 InitialVMSize (S n)
initVM instructions = VM 0 instructions (initTape _)

growVM : VMState left right is -> VMState left (ExtendedSize right) is
growVM {left} {right} vm =
  VM (pc vm) (instructions vm) extendedCells
  where
    extendedCells : Tape left (ExtendedSize right) (left + ExtendedSize right)
    extendedCells = extend (cells vm)

