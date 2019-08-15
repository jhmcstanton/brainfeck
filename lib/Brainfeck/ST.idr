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
  error    : String -> STrans m () res (const res)

export
CharIO IO where
  getChar  = lift getChar
  putChar  = lift . putChar
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

jumpBack : (vm : Var) -> ST id () [vm ::: VMST l r (S i)]
jumpBack = updateVM VM.jumpBack

jumpForward : (vm : Var) -> ST id () [vm ::: VMST l r (S i)]
jumpForward = updateVM VM.jumpForward

data StepResult : Type where
  StepError   : String -> StepResult
  StepSuccess : (l : Nat) -> (r : Nat) -> StepResult

ResultST : Type
ResultST = State StepResult

data AlwaysSucceeds : Type where
  STrivial : (l : Nat) -> (r : Nat) -> AlwaysSucceeds

AlwaysST : Type
AlwaysST = State StepResult

shiftLeft : CharIO io
          => (vm : Var)
          -> ST io StepResult [vm ::: VMST l r i :->
                                 (\res => case res of
                                            (StepError x) => VMST l r i
                                            (StepSuccess l' r') => VMST l' r' i)]
shiftLeft {l = Z} _ = do
  let msg = "Cell index is 0. Unable to leftshift."
  error msg
  pure $ StepError msg
shiftLeft {l = (S k)} {r} vm = update vm (VM.shiftLeft) >>= \_ => pure (StepSuccess k (S r))

shiftRight : {l : Nat} -> {r : Nat} -> {auto p : l + r = S k}
           -> (vm : Var)
           -> ST id AlwaysSucceeds [ vm ::: VMST l r i :->
                                      (\res => case res of
                                                 (STrivial l' r') => VMST l' r' i) ]
shiftRight {l = Z} {r = Z} {p = Refl} _ impossible
shiftRight {l = (S k)} {r = Z} vmVar =
  update vmVar (VM.shiftRight . grow) >>= \_ => pure (STrivial (S (S k)) k)
  where
    growProof : (vm : VMState llen (0 + (rlen + 0)) i) -> VMState llen rlen i
    growProof {rlen} vm = rewrite plusCommutative 0 rlen in vm
    grow : VMState (S k) 0 i -> VMState (S k) (S k) i
    grow vm = growProof (growVM vm)
shiftRight {l} {r = (S k)} vm = update vm VM.shiftRight >>= \_ => pure (STrivial (S l) k)

stepSuccess : {l : Nat} -> {r : Nat} -> StepResult
stepSuccess {l} {r} = StepSuccess l r

step : CharIO io => {result : Var} -> {auto p : l + r = S k }
     -> (vm : Var)
     -> STrans io StepResult [ vm ::: VMST l r (S i)]
        (\res => case res of
                   (StepError x)       => [ vm ::: VMST l  r  (S i) ]
                   (StepSuccess l' r') => [ vm ::: VMST l' r' (S i) ] )
step {l} {r} vmVar = do
  vm <- read vmVar
  case instruction vm of
    -- TLeft doesn't type check
    TLeft        => shiftLeft vmVar
    TRight       => shiftRight vmVar >>= \(STrivial l' r') => pure (StepSuccess {l=l'} {r=r'})
    TInc         => increment vmVar >>= \_ => pure stepSuccess
    TDec         => decrement vmVar >>= \_ => pure stepSuccess
    TOut         => outputChar vmVar >>= \_ => pure stepSuccess
    TIn          => readChar vmVar >>= \_ => pure stepSuccess
    TJumpForward => jumpForward vmVar >>= \_ => pure stepSuccess
    TJumpBack    => jumpBack vmVar >>= \_ => pure stepSuccess
