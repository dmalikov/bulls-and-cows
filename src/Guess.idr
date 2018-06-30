module Guess

import Data.Vect
import Data.So

import Digit
import Number

%default total
%access public export

data DigitState = Bull | Cow | Miss

Eq DigitState where
  Bull == Bull = True
  Cow == Cow = True
  Miss == Miss = True
  _ == _ = False

SecretNumber : Type
SecretNumber = Number

GuessNumber : Type
GuessNumber = Number

Match : Type
Match = Vect 4 DigitState

record GuessResult where
  constructor MkGuessRsult
  bulls, cows : Integer

evalGuess : GuessNumber -> SecretNumber -> GuessResult
evalGuess (MkNum (guess ** _)) (MkNum (actual ** _)) = eval (map evalEach zip')
  where
    evalEach : (Digit, Digit, Vect 4 Digit) -> DigitState
    evalEach (d1, d2, all) =
      if d1 == d2
         then Bull
         else
            if d1 `elem` all
               then Cow
               else Miss

    zip' : Vect 4 (Digit, Digit, Vect 4 Digit)
    zip' = zip3 guess actual (replicate 4 actual)

    eval : Match -> GuessResult
    eval = foldl (flip f) (MkGuessRsult 0 0) . toList
     where
      f : DigitState -> GuessResult -> GuessResult
      f Bull = record { bulls $= (+ 1) }
      f Cow = record { cows $= (+ 1) }
      f Miss = id
