module Brainfeck.ST

import Control.ST
import Data.Fin
import Data.Vect as V
import System

import Brainfeck.Type
import Brainfeck.VM as VM

%default total

export
interface CharIO (m : Type -> Type) where
  getChar  : STrans m Char res (const res)
  putChar  : Char -> STrans m () res (const res)
  -- complete : STrans m () res (const res)
  error    : String -> STrans m () res (const res)

export
CharIO IO where
  getChar  = lift getChar
  putChar  = lift . putChar
  -- complete = lift exitSuccess
  error    = lift . putStrLn

export
VMST : Nat -> Nat -> Nat -> Type
VMST l r i = State (VMState l r i)

export
InitVMST : Nat -> Type
InitVMST i = State (InitialVM i)

export
initST : CharIO io => Instructions (S n) -> ST io Var [add $ InitVMST (S n)]
initST instructions = do let vm = initVM instructions
                         new vm

readChar : CharIO io => (vm : Var) -> ST io () [vm ::: VMST l r i]
readChar vm = do c <- getChar
                 update vm (inputChar c)

outputChar : CharIO io => (vm : Var) -> ST io () [vm ::: VMST l r i]
outputChar vmVar = do
 vm <- read vmVar
 let cell = outputChar vm
 putChar cell

updateVM : (VMState l r i -> VMState l r i)
         -> (vm : Var)
         -> ST id () [vm ::: VMST l r i]
updateVM f vmVar = update vmVar f

increment : (vm : Var) -> ST id () [vm ::: VMST l r i]
increment = updateVM VM.increment

decrement : (vm : Var) -> ST id () [vm ::: VMST l r i]
decrement = updateVM VM.decrement

shiftLeft : CharIO io
          => (vm : Var)
          -> STrans io () [vm ::: VMST l r i]
               (\_ => case l of
                        Z    => [] -- failed
                        S l' => [vm ::: VMST l' (S r) i])
shiftLeft {l = Z} vm = do
  error "Cell index is 0. Unable to leftshift."
  delete vm
shiftLeft {l = (S k)} vm = update vm (VM.shiftLeft)

VMShiftedRight : (l : Nat) -> (r : Nat) -> (p : l + r = S k) -> (i : Nat) -> Type
VMShiftedRight Z Z Refl _ impossible
VMShiftedRight (S k) Z _ i = VMST (S (S k)) k i
VMShiftedRight l (S k) _ i = VMST (S l) k i


shiftRight : {l : Nat} -> {r : Nat} -> {auto p : l + r = S k}
           -> (vm : Var)
           -> ST io () [ vm ::: VMST l r i :-> VMShiftedRight l r p i ]
shiftRight {l = Z} {r = Z} {p = Refl} _ impossible
shiftRight {l = (S k)} {r = Z} vmVar = update vmVar (VM.shiftRight . grow) where
  growProof : (vm : VMState llen (0 + (rlen + 0)) i) -> VMState llen rlen i
  growProof {rlen} vm = rewrite plusCommutative 0 rlen in vm
  grow : VMState (S k) 0 i -> VMState (S k) (S k) i
  grow vm = growProof (growVM vm)
shiftRight {r = (S k)} vm = update vm VM.shiftRight
