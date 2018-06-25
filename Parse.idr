module Parse

import Data.Vect
import Data.So
import Effects
import Effect.Exception

import Digit
import Number

%default total
%access public export

data NumberError = NotANumber | TooFewDigits | TooManyDigits | HasDuplicates

parseNumber : String -> Eff Number [EXCEPTION NumberError]
parseNumber str =
  if all isDigit (unpack str)
     then case catMaybes $ map fromChar $ unpack str of
               num@[_,_,_,_] => let v = the (Vect 4 Digit) num
                                in case choose (allUnique v) of
                                        Left p => pure (MkNum (v ** p))
                                        Right => raise HasDuplicates
               xs => if length xs < 4
                        then raise TooFewDigits
                        else raise TooManyDigits
     else raise NotANumber
