module Brainfeck.Util

import Data.Vect

%default total

export
listToVect : List a -> (num_a : Nat ** Vect num_a a)
listToVect []        = (0 ** Nil)
listToVect (a :: as) =
  case listToVect as of
    (_ ** avect) => (_ ** a :: avect)
