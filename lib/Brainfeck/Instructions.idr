module Brainfeck.Instructions

import Data.Vect as V

import Brainfeck.Type

-- TODO: Implement this at some point

%default total

-- TODO: Possibly mae index : Fin n, so its always bounded by the length of instrutions.
-- How to encode that in the constructor?
data Instructions : (index : Nat) -> Vect n Token -> Type where
  Ins : (prev : Vect index Token) -> (remaining : Vect rLen Token) -> Instructions (V.length prev) (reverse prev ++ remaining)

%name Instructions instructions

instructions : (is : Vect n Token) -> Instructions 0 is
instructions is = Ins [] is

current : {auto p: LT pc (V.length is) } -> Instructions pc is -> Token
-- current (Ins prev (cur :: is)) = cur

step : {auto p : LT pc (V.length is)} -> Instructions pc is -> Instructions (S pc) is
-- step (Ins prev (cur :: rem)) = ?stepPrf $ Ins (cur :: prev) rem

jump : (next : Nat) -> Instructions pc is -> Instructions next is

