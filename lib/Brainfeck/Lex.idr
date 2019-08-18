module Brainfeck.Lex

import Data.Vect as V

import Brainfeck.Type
import Brainfeck.Util

%default total

token : Char -> Maybe Token
token '<' = Just TLeft
token '>' = Just TRight
token '+' = Just TInc
token '-' = Just TDec
token '.' = Just TOut
token ',' = Just TIn
token '[' = Just TJumpForward
token ']' = Just TJumpBack
token _   = Nothing

lexLine : (line : Nat) -> (col : Nat) -> List Char -> (num_tokens : Nat ** Tokens num_tokens)
lexLine _    _    [] = (0 ** [])
lexLine line col (c :: cs) =
  case lexLine line (col + 1) cs of
    (_ ** tokens) => case token c of
                       Nothing => (_ ** tokens)
                       Just t  => (_ ** (Loc line col, t) :: tokens)

-- Lines are lexed in reverse order to preverse line numbers
-- Note, the contents of the lines should _not_ be reversed
lexList : Vect line_no (List Char) -> (num_tokens : Nat ** Tokens num_tokens)
lexList [] = (0 ** [])
lexList {line_no = S n} (cs :: lines) =
  case lexList lines of
    (_ ** otherTokens) => case lexLine (S n) 0 cs of
                            (_ ** tokens) => (_ ** (reverse tokens) ++ otherTokens)

export
lex : (program : String) -> (num_tokens ** Tokens num_tokens)
lex program =
    let lines = listToVect . map unpack . reverse . lines $ program in
    case lines of
      (_ ** ls) => case lexList ls of
                     (_ ** ts) => (_ ** reverse ts)
