import Data.Vect
import System

import Digit
import Number
import Guess

%default total

data Input = InGuess GuessNumber
           | InAdmit

strToInput : String -> Maybe Input
strToInput str =
  case words str of
       "admit" :: _ => Just InAdmit
       "guess" :: num :: Nil => map InGuess (fromStr num)
       _ => Nothing

data GameState : Type where
  NotRunning : GameState
  Running : SecretNumber -> GameState

data GameCmd : (ty : Type) -> (prev_state : GameState) -> (new_state : GameState) -> Type where
  Won : GameCmd () (Running secret) NotRunning
  Admitted : GameCmd () (Running secret) NotRunning
  Message : String -> GameCmd () state state
  GetInput : GameCmd (Maybe Input) (Running secret) (Running secret)

  Pure : (res : ty) -> GameCmd ty state state
  (>>=) : GameCmd a state1 state2 -> (a -> GameCmd b state2 state3) -> GameCmd b state1 state3

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> GameState -> Type where
    (>>=) : GameCmd a state1 state2
         -> (a -> Inf (GameLoop b state2 state3))
         -> GameLoop b state1 state3
    Exit : GameLoop () state NotRunning

gameLoop : GameLoop () (Running secret) NotRunning
gameLoop {secret} = do
  input <- GetInput
  case input of
       Just (InGuess guess) => do
         let result = evalGuess guess secret
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
       _ => do
         Message "Invalid input"
         gameLoop

data GameResult : (ty : Type) -> GameState -> Type where
  OK : (res : ty) -> GameResult ty outstate
  OutOfFuel : GameResult ty outstate

namespace Combinations
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

random : Int -> Int
random seed = (1664525 * seed + 1013904223) `shiftR` 2

partial -- todo
initSecret : IO SecretNumber
initSecret = do
  timestamp <- time
  let combs = combinations 4 [D0,D1,D2,D3,D4,D5,D6,D7,D8,D9]
  let idx = fromIntegerNat (timestamp `mod` (toIntegerNat (length combs)))
  case index' idx combs of
       Just secret => pure $ MkNum secret
       Nothing => pure $ MkNum [D1,D2,D3,D4]

data Fuel = Dry | More (Lazy Fuel)

runCmd : GameCmd ty prev_state next_state -> IO ty
runCmd Won = putStrLn "Correct, you win!"
runCmd Admitted {prev_state = Running secret} = putStrLn ("The secret number was " ++ show secret)
runCmd GetInput = do putStr "> "
                     x <- getLine
                     pure $ strToInput x
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
main = do n <- initSecret
          run forever (do Message "Try to guess the secret number. \"guess <num>\" to guess, \"admit\" to admit."
                          gameLoop {secret = n})
          pure ()
