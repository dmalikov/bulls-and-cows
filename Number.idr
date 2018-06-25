module Number

import Data.Vect

import Digit
import Digit

%access public export
%default total

data Number : Type where
  MkNum : Vect 4 Digit -> Number

Show Number where
  show (MkNum xs) = concatMap show xs
