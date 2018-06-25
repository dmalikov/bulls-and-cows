module Input

import Effects
import Effect.Exception

import Guess
import Number
import Parse

%default total
%access public export

data Input = InGuess GuessNumber
           | InAdmit

data InputError = UnsupportedCommand String | MalformedGuess NumberError

parseInput : String -> Eff Input [EXCEPTION InputError]
parseInput str =
  case words str of
       "admit" :: _ => pure InAdmit
       "guess" :: num :: Nil => case the (Either NumberError Number) (run (parseNumber num)) of
                                     Left e => raise (MalformedGuess e)
                                     Right n => pure (InGuess n)
       _ => raise (UnsupportedCommand str)
