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

data SecretInitError = DuplicateDigitsGenerated

partial
rand4Digits : Eff (Vect 4 Digit) [SYSTEM, RND]
rand4Digits = do
  srand !time
  (el1, l1) <- f [D9,D0,D8,D1,D7,D2,D6,D3,D5,D4]
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
