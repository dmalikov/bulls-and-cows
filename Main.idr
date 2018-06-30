import Data.Vect
import Effects
import Effect.Exception
import System

import Digit
import Guess
import Input
import Number
import Parse
import Random

%default total

data GameState : Type where
  NotRunning : GameState
  Running : SecretNumber -> (startTime : Integer) -> (attCnt : Nat) -> GameState

data GameCmd : (ty : Type) -> (prev_state : GameState) -> (new_state : GameState) -> Type where
  Won : GameCmd () (Running s t ac) NotRunning
  Admitted : GameCmd () (Running s t ac) NotRunning
  Guess : GuessNumber -> GameCmd GuessResult (Running s t ac) (Running s t (S ac))
  Message : String -> GameCmd () state state
  GetInput : GameCmd (Maybe Input) (Running s t ac) (Running s t ac)

  Pure : (res : ty) -> GameCmd ty state state
  (>>=) : GameCmd a state1 state2 -> (a -> GameCmd b state2 state3) -> GameCmd b state1 state3

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> GameState -> Type where
    (>>=) : GameCmd a state1 state2
         -> (a -> Inf (GameLoop b state2 state3))
         -> GameLoop b state1 state3
    Exit : GameLoop () state NotRunning

gameLoop : GameLoop () (Running secret startTime attCnt) NotRunning
gameLoop {secret} {startTime} {attCnt} = do
  input <- GetInput
  case input of
       Just (InGuess guess) => do
         result <- Guess guess
         if (bulls result == 4)
            then do
              Won
              Exit
            else do
              Message (show (bulls result) ++ " bulls, " ++ show (cows result) ++ " cows")
              gameLoop
       Just InAdmit => do
         Admitted
         Exit
       _ => gameLoop

data GameResult : (ty : Type) -> GameState -> Type where
  OK : (res : ty) -> GameResult ty outstate
  OutOfFuel : GameResult ty outstate

data Fuel = Dry | More (Lazy Fuel)

runCmd : GameCmd ty prev_state next_state -> IO ty
runCmd Won {prev_state = Running secret startTime attCnt} = do
  curTime <- time
  putStrLn $ "Correct! It took " ++ show (curTime - startTime) ++ " sec and " ++ show (toIntegerNat attCnt) ++ " attempts."
runCmd Admitted {prev_state = Running secret startTime attCnt} = do
  curTime <- time
  putStrLn $ "The secret number was " ++ show secret ++ ". Admitted after " ++ show (curTime - startTime) ++ " sec and " ++ show (toIntegerNat attCnt) ++ " attempts."
runCmd GetInput {prev_state = Running _ _ attCnt} = do
  putStr $ "guess " ++ show (toIntegerNat (S attCnt)) ++ ": "
  x <- getLine
  case the (Either InputError Input) (run (parseInput x)) of
       Left (UnsupportedCommand str) => do putStrLn ("Unsupported command: '" ++ str ++ "'"); pure Nothing
       Left (MalformedGuess NotANumber) => do putStrLn "Invalid input: not a number"; pure Nothing
       Left (MalformedGuess TooFewDigits) => do putStrLn "Invalid input: too few digits"; pure Nothing
       Left (MalformedGuess TooManyDigits) => do putStrLn "Invalid input: too many digits"; pure Nothing
       Left (MalformedGuess HasDuplicates) => do putStrLn "Invalid input: number cannot have duplicate gidits"; pure Nothing
       Right input => pure (Just input)
runCmd (Guess guess) {prev_state = Running secret _ _ } = pure (evalGuess guess secret)
runCmd (Message message) = putStrLn message
runCmd (Pure res) = pure res
runCmd (x >>= f) = do y <- runCmd x
                      runCmd (f y)

run : Fuel -> GameLoop ty instate outstate -> IO ()
run Dry _ = pure ()
run (More fuel) (cmd >>= next)
  = do res <- runCmd cmd
       run fuel (next res)
run (More fuel) Exit = pure ()

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do
  secret <- initSecret
  case secret of
       Left DuplicateDigitsGenerated =>
         putStrLn "This shouldn't happen, duplicate digits generated, exiting"
       Right n => do
         startTime <- time
         run forever (do Message "Try to guess the secret number. \"guess <num>\" to guess, \"admit\" to admit."
                         gameLoop {secret = n} {startTime = startTime} {attCnt = Z})
         pure ()
