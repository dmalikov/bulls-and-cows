module Random

import Data.Vect
import Effects
import Effect.Exception
import Effect.Random
import Effect.Select
import Effect.System

import Digit
import Guess
import Number

%default total
%access public export

combinations : (n : Nat) -> List a -> List (Vect n a)
combinations n = catMaybes . map (f n) . c n
  where
    f : (n : Nat) -> (xs : List a) -> Maybe (Vect n a)
    f n xs with (decEq (length xs) n)
      | (Yes prf) = rewrite (sym prf) in Just (fromList xs)
      | (No _) = Nothing
    c : Nat -> List a -> List (List a)
    c Z _ = [[]]
    c _ [] = [[]]
    c (S k) (x :: xs) = map (x ::) (c k xs) ++ c (S k) xs

maybeToList : Maybe a -> List a
maybeToList (Just a) = [a]
maybeToList Nothing = []

data SecretInitError = SystemError | DuplicateDigitsGenerated

partial
initSecret : IO (Either SecretInitError SecretNumber)
initSecret = do
  el <- the (IO (Maybe (Vect 4 Digit))) (run randVect4)
  case el of
       Nothing => pure (Left SystemError)
       Just el => case choose (allUnique el) of
                       Left p => pure (Right (MkNum (el ** p)))
                       Right _ => pure (Left DuplicateDigitsGenerated)
 where
  partial
  randVect4 : Eff (Maybe (Vect 4 Digit)) [SYSTEM, RND]
  randVect4 = do
    srand !time
    rndSelect (combinations 4 [D0,D1,D2,D3,D4,D5,D6,D7,D8,D9])
