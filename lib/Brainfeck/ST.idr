module Brainfeck.ST

import Control.ST
import Data.Fin
import Data.Vect as V

import Brainfeck.Type
import Brainfeck.VM

%default total

interface CharIO (m : Type -> Type) where
  getChar : STrans m Char res (const res)
  putChar : Char -> STrans m () res (const res)

CharIO IO where
  getChar = lift getChar
  putChar = lift . putChar
