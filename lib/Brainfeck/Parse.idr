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
  TOp  : Operation -> Location -> TempOp
  TJZ  : Nat -> Location -> TempOp
  TJNZ : Nat -> Location -> TempOp

mkParseError : TempOp -> String -> ParseError
mkParseError (TOp  _ loc) err = MkParseError loc err
mkParseError (TJZ  _ loc) err = MkParseError loc err
mkParseError (TJNZ _ loc) err = MkParseError loc err

tokenToTOp : Token -> Location -> Nat -> TempOp
tokenToTOp TLeft loc _        = TOp OLeft loc
tokenToTOp TRight loc _       = TOp ORight loc
tokenToTOp TInc loc _         = TOp OInc loc
tokenToTOp TDec loc _         = TOp ODec loc
tokenToTOp TOut loc _         = TOp OOut loc
tokenToTOp TIn loc _          = TOp OIn loc
tokenToTOp TJumpForward loc i = TJZ i loc
tokenToTOp TJumpBack loc i    = TJNZ i loc

tempToOp : (numOps : Nat) -> TempOp -> Maybe Operation
tempToOp _      (TOp op _) = Just op
tempToOp numOps (TJZ  l _) = map OJumpZero  $ natToFin l numOps
tempToOp numOps (TJNZ l _) = map OJumpNZero $ natToFin l numOps

goLoop : Tokens n -> (is : Var) -> (forwards : Var) -> (opNo : Var)
       -> ST id (Either ParseError (List TempOp))
            [ is ::: State (List TempOp),
              forwards ::: State (List TempOp),
              opNo ::: State Nat ]
goLoop [] is forwards _ = do
  fs <- read forwards
  case fs of
    Nil       => read is >>= \is => pure (Right $ reverse is)
    (f :: fs) => pure (Left $ mkParseError f "Unmatched forward jump")
goLoop ((loc, t) :: xs) is forwards iVar = do
  i <- read iVar
  update iVar (+1)
  let tOp = tokenToTOp t loc i
  case tOp of
    TJZ  _ l => do
      update forwards (tOp ::)
      update is (tOp ::)
      goLoop xs is forwards iVar
    TJNZ _ l => do
      fs <- read forwards
      case fs of
        Nil        => pure (Left $ MkParseError loc "Unmatched backward jump")
        (_ :: rem) => do
          write forwards rem
          update is (tOp ::)
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
    (Right (n ** vs)) => --pure $ Right (_ ** map (tempToOp n) vs)
      let (m ** converted) = mapMaybe (tempToOp n) vs in
      case decEq n m of
        (Yes prf   ) => pure . Right $ (m ** converted)
        (No  contra) =>
          pure . Left $ MkParseError (Loc 0 0) "Labels not bounded by number of operations."

export
parse : Tokens n -> Either ParseError (n : Nat ** Instructions n)
parse tokens = runPure (go tokens)

