module Brainfeck.Parse
-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
import Control.ST
import Data.Vect as V

import Brainfeck.Type
import Brainfeck.Util

%default total

public export
data ParseError : Type where
  MkParseError  : Location -> String -> ParseError

data TempOp : Type where
  TOp  : Operation n -> Location -> TempOp
  TJZ  : Nat -> Location -> TempOp
  TJNZ : Nat -> Location -> TempOp

mkParseError : TempOp -> String -> ParseError
mkParseError (TOp  _ loc) err = MkParseError loc err
mkParseError (TJZ  _ loc) err = MkParseError loc err
mkParseError (TJNZ _ loc) err = MkParseError loc err

tokenToTOp : Token -> Location -> Nat -> TempOp
tokenToTOp TLeft loc _        = TOp OLeft {n=0} loc
tokenToTOp TRight loc _       = TOp ORight {n=0}loc
tokenToTOp TInc loc _         = TOp OInc {n=0} loc
tokenToTOp TDec loc _         = TOp ODec {n=0} loc
tokenToTOp TOut loc _         = TOp OOut {n=0} loc
tokenToTOp TIn loc _          = TOp OIn {n=0} loc
tokenToTOp TJumpForward loc i = TJZ i loc
tokenToTOp TJumpBack loc i    = TJNZ i loc

tempToOp : (numOps : Nat) -> TempOp -> Maybe (Operation numOps)
tempToOp _      (TOp OLeft  _) = Just OLeft
tempToOp _      (TOp ORight _) = Just ORight
tempToOp _      (TOp OInc   _) = Just OInc
tempToOp _      (TOp ODec   _) = Just ODec
tempToOp _      (TOp OOut   _) = Just OOut
tempToOp _      (TOp OIn    _) = Just OIn
tempToOp _      (TOp _      _) = Nothing
tempToOp numOps (TJZ  l _) = map OJumpZero  $ natToFin l numOps
tempToOp numOps (TJNZ l _) = map OJumpNZero $ natToFin l numOps

matchForwardJump : (jumpTo : Nat) -> TempOp -> TempOp
matchForwardJump n (TJZ _ loc) = TJZ n loc
matchForwardJump _ anything = anything

updateListElem : (a -> a) -> (idx : Nat) -> List a -> List a
updateListElem f n xs = go f (length xs `minus` S n) xs where
  go _ _ [] = []
  go f Z (x :: xs) = f x :: xs
  go f (S n) (x :: xs) = x :: go f n xs

goLoop : Tokens n -> (is : Var) -> (forwards : Var) -> (opNo : Var)
       -> ST id (Either ParseError (List TempOp))
            [ is ::: State (List TempOp),
              forwards ::: State (List (TempOp, Nat)),
              opNo ::: State Nat ]
goLoop [] is forwards _ = do
  fs <- read forwards
  case fs of
    Nil       => read is >>= \is => pure (Right $ reverse is)
    (f :: fs) => pure (Left $ mkParseError (fst f) "Unmatched forward jump")
goLoop ((loc, t) :: xs) is forwards iVar = do
  i <- read iVar
  update iVar (+1)
  let tOp = tokenToTOp t loc i
  case tOp of
    TJZ  _ l => do
      update forwards ((TJZ i l, i) ::)
      -- remember to update these when the matching bracket is found
      update is ((TJZ 0 l) ::)
      goLoop xs is forwards iVar
    TJNZ _ l => do
      fs <- read forwards
      case fs of
        Nil        => pure (Left $ MkParseError loc $ "Unmatched backward jump " ++ show i)
        ((_, prev) :: rem) => do
          write forwards rem
          update is ((TJNZ prev l) ::)
          update is (updateListElem (matchForwardJump i) prev)
          goLoop xs is forwards iVar
    _      => update is (tOp ::) >>= \_ => goLoop xs is forwards iVar

go : Tokens n -> ST id (Either ParseError (n : Nat ** Instructions n)) []
go ts = do
  is <- new Nil
  fs <- new Nil
  i  <- new Z

  instructionList <- call $ goLoop ts is fs i
  let instructionVect = map listToVect instructionList
  delete is
  delete fs
  delete i
  case instructionVect of
    (Left l) => pure $ Left l
    (Right (n ** vs)) =>
      let (m ** converted) = mapMaybe (tempToOp n) vs in
      case decEq n m of
        (Yes Refl   ) => pure . Right $ (n ** converted)
        (No  contra) =>
          pure . Left $ MkParseError (Loc 0 0) "Labels not bounded by number of operations."

export
parse : Tokens n -> Either ParseError (n : Nat ** Instructions n)
parse tokens = runPure (go tokens)

