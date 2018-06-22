module Number

import Data.Vect

import Digit

%access public export
%default total

allUnique : Eq a => List a -> Bool
allUnique xs = length (nub xs) == length xs

data Number : Type where
  MkNum : Vect 4 Digit -> Number

fromStr : String -> Maybe Number
fromStr str with (toIntegerNat $ length str)
  | 4 = case catMaybes $ map fromChar $ unpack str of
             num@[d1,d2,d3,d4] => if allUnique [d1,d2,d3,d4]
                                     then Just (MkNum num)
                                     else Nothing
             _ => Nothing
  | _ = Nothing


Show Number where
  show (MkNum xs) = concatMap show xs
