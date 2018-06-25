module Number

import Data.Vect
import Data.So

import Digit

%access public export
%default total

allUnique : Eq a => Vect n a -> Bool
allUnique xs = let (_ ** unique) = nub xs
               in length unique == length xs

data Number : Type where
  MkNum : (xs : Vect 4 Digit ** So (allUnique xs)) -> Number

Show Number where
  show (MkNum (xs ** _)) = concatMap show xs
