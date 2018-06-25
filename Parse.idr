module Parse

import Data.Vect
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
               num@[d1,d2,d3,d4] => if allUnique [d1,d2,d3,d4]
                                       then pure (MkNum num)
                                       else raise HasDuplicates
               xs => if length xs < 4
                        then raise TooFewDigits
                        else raise TooManyDigits
     else raise NotANumber
    where
      allUnique : Eq a => List a -> Bool
      allUnique xs = length (nub xs) == length xs
