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

data SecretInitError = DuplicateDigitsGenerated

partial
rand4Digits : Eff (Vect 4 Digit) [SYSTEM, RND]
rand4Digits = do
  srand !time
  (el1, l1) <- f digits
  (el2, l2) <- f l1
  (el3, l3) <- f l2
  (el4, _ ) <- f l3
  pure [el1, el2, el3, el4]
 where
  partial
  f : Vect (S k) Digit -> Eff (Digit, Vect k Digit) [RND]
  f {k} xs = do
    ix <- rndFin k
    pure (index ix xs, deleteAt ix xs)

partial
initSecret : IO (Either SecretInitError SecretNumber)
initSecret = do
  number <- run rand4Digits
  case choose (allUnique number) of
       Left p => pure (Right (MkNum (number ** p)))
       Right _ => pure (Left DuplicateDigitsGenerated)
