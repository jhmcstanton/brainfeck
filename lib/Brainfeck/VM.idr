module Brainfeck.VM

import Data.Fin
import Data.Vect as V
import Prelude.List as L

import Brainfeck.Type

%default total

export
Cell : Type
Cell = Int

export
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

  set_current : Cell -> Tape left right size -> Tape left right size
  set_current c' (MkTape l c r) = MkTape l c' r

  initTape : (size : Nat) -> Tape 0 size size
  initTape size = MkTape V.Nil 0 (V.replicate size 0)

  shiftLeft : Tape (S l) r ((S l) + r) -> Tape l (S r) (l + (S r))
  shiftLeft {l} {r} (MkTape (x :: xs) c ys) = tape'
    where
      tape' = MkTape xs x (c :: ys)

  shiftRight : Tape l (S r) (l + (S r)) -> Tape (S l) r ((S l) + r)
  shiftRight {l} {r} (MkTape xs c (y :: ys)) = tape'
    where
      tape' = MkTape (c :: xs) y ys

  extend : Tape left right (left + right) -> Tape left (right + k) (left + (right + k))
  extend {left} {right} {k} (MkTape xs c ys) = tape' where
    tape' = MkTape xs c (extendVect ys)
    extendVect : Vect n Cell -> Vect (n + k) Cell
    extendVect [] = replicate _ 0
    extendVect (x :: xs) = x :: extendVect xs

public export
record VMState (tapeLeft : Nat) (tapeRight : Nat) (instructionCount : Nat) where
  constructor    VM
  pc           : Fin instructionCount
  instructions : Instructions instructionCount
  cells        : Tape tapeLeft tapeRight (tapeLeft + tapeRight)
%name VMState vm

export
instruction : VMState l r i -> Operation i
instruction vm = index (pc vm) (instructions vm)

public export
InitialVMSize : Nat
InitialVMSize = 1000

public export
InitialVM : (instructionCount : Nat) -> Type
InitialVM instructionCount = VMState 0 InitialVMSize instructionCount

export
initVM : Instructions (S n) -> InitialVM (S n)
initVM instructions = VM 0 instructions (initTape _)

export
growVM : (vm : VMState left right is) -> VMState left (right + (left + right)) is
growVM {left} {right} vm =
  VM (pc vm) (instructions vm) extendedCells
  where
    extendedCells : Tape left (right + (left + right)) (left + (right + (left + right)))
    extendedCells = extend (cells vm) {k = left + right}

-------------------------------------------------
-- Operations
-------------------------------------------------

-- <
export
shiftLeft : VMState (S left) right is -> VMState left (S right) is
shiftLeft {left} {right} vm = VM (pc vm) (instructions vm) cells' where
  cells' = Tape.shiftLeft . cells $ vm

-- >
-- This was going to also increase the size of the vm if Right = Z, but
-- that really complicates the type.
export
shiftRight : VMState left (S right) is -> VMState (S left) right is
shiftRight {right} vm = VM (pc vm) (instructions vm) cells' where
  cells' = Tape.shiftRight . cells $ vm

updateCell : (Cell -> Cell) -> VMState left right is -> VMState left right is
updateCell f = record { cells->current $= f }

-- +
export
increment : VMState left right is -> VMState left right is
increment = updateCell (+1)

-- -
export
decrement : VMState left right is -> VMState left right is
decrement = updateCell (\c => c - 1)

-- .
export
outputChar : VMState left right is -> Char
outputChar = chr . record { cells->current }

-- ,
export
inputChar : Char -> VMState left right is -> VMState left right is
inputChar c = record { cells->current = (ord c) }

-- [
export
jumpBack : VMState left right (S is) -> VMState left right (S is)
jumpBack vm =
  case instruction vm of
    OJumpNZero l => if record { cells->current } vm == 0
                    then vm
                    else record { pc = l } vm
    _            => vm

-- ]
export
jumpForward : VMState left right (S is) -> VMState left right (S is)
jumpForward vm =
  case instruction vm of
    OJumpZero l => if record { cells->current } vm == 0
                   then record { pc = l } vm
                   else vm
    _           => vm
