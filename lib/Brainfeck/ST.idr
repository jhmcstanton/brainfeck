module Brainfeck.ST

import Control.ST
import Data.Fin
import Data.Vect as V
import System

import Brainfeck.Lex
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

-- export
-- CharIO JS_IO where
--   getChar  = ?rhs
--   putChar  = ?rhs
--   error    = ?rhs

export
VMST : Nat -> Nat -> Nat -> Type
VMST l r i = State (VMState l r i)

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
  StepError   : String -> (l : Nat) -> (r : Nat) -> (i : Nat) -> StepResult
  StepSuccess : (l : Nat) -> (r : Nat) -> (i : Nat) -> StepResult

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
                                            (StepError e l r i)   => VMST l r i
                                            (StepSuccess l' r' i) => VMST l' r' i)]
shiftLeft {l = Z} {r} {i} _ = do
  let msg = "Cell index is 0. Unable to leftshift."
  error msg
  pure $ StepError msg Z r i
shiftLeft {l = (S k)} {r} {i} vm = update vm (VM.shiftLeft) >>= \_ => pure (StepSuccess k (S r) i)

shiftRight : {l : Nat} -> {r : Nat} -> {auto p : IsSucc (l + r)}
           -> (vm : Var)
           -> ST id AlwaysSucceeds [ vm ::: VMST l r i :->
                                      (\res => case res of
                                                 (STrivial l' r') => VMST l' r' i) ]
shiftRight {l = (S k)} {r = Z} vmVar =
  update vmVar (VM.shiftRight . grow) >>= \_ => pure (STrivial (S (S k)) k)
  where
    growProof : (vm : VMState llen (0 + (rlen + 0)) i) -> VMState llen rlen i
    growProof {rlen} vm = rewrite plusCommutative 0 rlen in vm
    grow : VMState (S k) 0 i -> VMState (S k) (S k) i
    grow vm = growProof (growVM vm)
shiftRight {l} {r = (S k)} vm = update vm VM.shiftRight >>= \_ => pure (STrivial (S l) k)

stepSuccess : {l : Nat} -> {r : Nat} -> {i : Nat} -> StepResult
stepSuccess {l} {r} {i} = StepSuccess l r i

step : CharIO io => {auto p : IsSucc (l + r) }
     -> (vm : Var)
     -> ST io StepResult [ vm ::: VMST l r (S i) :->
                                (\res => case res of
                                           (StepError e l  r  i) => VMST l  r  i
                                           (StepSuccess l' r' i) => VMST l' r' i) ]
step {l} {r} {i} vmVar = do
  vm <- read vmVar
  case instruction vm of
    TLeft        => do vm' <- shiftLeft vmVar
                       case vm' of
                         (StepError e l  r  i) => pure $ StepError e l r i
                         (StepSuccess l' r' i) => pure $ StepSuccess l' r' i
    TRight       => shiftRight vmVar >>= \(STrivial l' r') => pure (StepSuccess l' r' (S i))
    TInc         => increment vmVar >>= \_ => pure stepSuccess
    TDec         => decrement vmVar >>= \_ => pure stepSuccess
    TOut         => outputChar vmVar >>= \_ => pure stepSuccess
    TIn          => readChar vmVar >>= \_ => pure stepSuccess
    TJumpForward => jumpForward vmVar >>= \_ => pure stepSuccess
    TJumpBack    => jumpBack vmVar >>= \_ => pure stepSuccess

partial -- :(
runLoop : CharIO io => {auto p : IsSucc (l + r) } -> (vm : Var) -> ST io () [ remove vm (VMST l r (S i)) ]
runLoop vmVar = do
  -- TODO: remove the next 2 lines
  -- v <- read vmVar
  -- error $ "PC: " ++ (show . finToNat . pc $ v) ++ " Ins: " ++ (toS $ instruction v) ++ " " ++ VM.JumpLabels.toS (jumps v)
  res <- step vmVar
  case res of
    (StepError _ _ _ (S k)) => error "Aborting" >>= \_ => delete vmVar
    (StepError _ _ _  Z   ) => error "Ended up in an undefined state (missing all instructions)" >>= \_ => delete vmVar
    (StepSuccess _ _  Z   ) => do error "Ended up in an undefined state (missing all instructions) after successful step"
                                  delete vmVar
    (StepSuccess tapeL tapeR (S k)) => do
      case isItSucc (tapeL + tapeR) of
         No _    => error "Somehow the tape was deleted. Aborting." >>= \_ => delete vmVar
         Yes prf => do
           vm <- read vmVar
           let pc' = FS (pc vm)
           case strengthen pc' of
             (Left l) => delete vmVar -- end of program
             (Right r) => do
               update vmVar (record { pc = r })
               runLoop vmVar

partial
export
-- TODO: Make this generic per backend
-- IO -> IO' lang
runProgram : String -> IO ()
runProgram progText =
  case lex progText of
    (Z ** _ ) => putStrLn "Nothing to do. Bye"
    (S n ** ts) => do
      let vm = initVM ts
      case isItSucc InitialVMSize of
        (No _)    => putStrLn "This was compiled with an invalid InitialVMSize! See ya."
        (Yes prf) => run (do
                       v <- new vm
                       runLoop {p = prf} {l = 0} {r = InitialVMSize} v)

