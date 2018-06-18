import Data.Vect
import System

%default total

namespace Digit

  data Digit = D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9

  Eq Digit where
    D0 == D0 = True
    D1 == D1 = True
    D2 == D2 = True
    D3 == D3 = True
    D4 == D4 = True
    D5 == D5 = True
    D6 == D6 = True
    D7 == D7 = True
    D8 == D8 = True
    D9 == D9 = True
    _ == _ = False

  fromChar : Char -> Maybe Digit
  fromChar '0' = Just D0
  fromChar '1' = Just D1
  fromChar '2' = Just D2
  fromChar '3' = Just D3
  fromChar '4' = Just D4
  fromChar '5' = Just D5
  fromChar '6' = Just D6
  fromChar '7' = Just D7
  fromChar '8' = Just D8
  fromChar '9' = Just D9
  fromChar _ = Nothing

  Show Digit where
    show D0 = "0"
    show D1 = "1"
    show D2 = "2"
    show D3 = "3"
    show D4 = "4"
    show D5 = "5"
    show D6 = "6"
    show D7 = "7"
    show D8 = "8"
    show D9 = "9"

allUnique : Eq a => List a -> Bool
allUnique xs = length (nub xs) == length xs

namespace Number

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

data DigitState = Bull | Cow | Miss

Eq DigitState where
  Bull == Bull = True
  Cow == Cow = True
  Miss == Miss = True
  _ == _ = False

data GuessResult : Type where
  Correct : GuessResult
  Incorrect : (bulls : Nat) -> (cows : Nat) -> GuessResult -- bulls are <= 4, cows are <= 4, cows + bulls <= 4

evalGuess : (guess : Number) -> (actual : Number) -> GuessResult
evalGuess (MkNum guess) (MkNum actual) = decide (map evalEach zip')
  where
    evalEach : (Digit, Digit, Vect 4 Digit) -> DigitState
    evalEach (d1, d2, all) =
      if d1 == d2
         then Bull
         else
            if d1 `elem` all
               then Cow
               else Miss

    decide : Vect 4 DigitState -> GuessResult
    decide (Bull :: Bull :: Bull :: Bull :: Nil) = Correct
    decide xs = Incorrect (fst $ Vect.filter (== Bull) xs) (fst $ Vect.filter (== Cow) xs)

    zip' : Vect 4 (Digit, Digit, Vect 4 Digit)
    zip' = zip3 guess actual (replicate 4 actual)

data Input = InGuess Number
           | InAdmit

strToInput : String -> Maybe Input
strToInput str =
  case words str of
       "admit" :: _ => Just InAdmit
       "guess" :: num :: Nil => map InGuess (fromStr num)
       _ => Nothing

data GameState : Type where
  NotRunning : GameState
  Running : (number : Number) -> GameState

data GameCmd : (ty : Type) -> (prev_state : GameState) -> (new_state : GameState) -> Type where
  Won : GameCmd () (Running number) NotRunning
  Admitted : GameCmd () (Running number) NotRunning
  Message : String -> GameCmd () state state
  GetInput : GameCmd (Maybe Input) (Running number) (Running number)

  Pure : (res : ty) -> GameCmd ty state state
  (>>=) : GameCmd a state1 state2 -> (a -> GameCmd b state2 state3) -> GameCmd b state1 state3

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> GameState -> Type where
    (>>=) : GameCmd a state1 state2
         -> (a -> Inf (GameLoop b state2 state3))
         -> GameLoop b state1 state3
    Exit : GameLoop () state NotRunning

gameLoop : GameLoop () (Running number) NotRunning
gameLoop {number} = do
  input <- GetInput
  case input of
       Just (InGuess guess) => do
         case evalGuess guess number of
              Correct => do
                Won
                Exit
              Incorrect {bulls} {cows} => do
                Message (show bulls ++ " bulls, " ++ show cows ++ " cows")
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
initNumber : IO Number
initNumber = do
  timestamp <- time
  let combs = combinations 4 [D0,D1,D2,D3,D4,D5,D6,D7,D8,D9]
  case take 1 $ drop (fromIntegerNat (timestamp `mod` (toIntegerNat (length combs)))) combs of
       [] => pure $ MkNum [D1,D2,D3,D4]
       number :: _ => pure $ MkNum number

data Fuel = Dry | More (Lazy Fuel)

runCmd : GameCmd ty prev_state next_state -> IO ty
runCmd Won = putStrLn "Correct, you win!"
runCmd Admitted {prev_state = Running number} = putStrLn ("The number was " ++ show number)
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
main = do n <- initNumber
          run forever (do Message "I've came with some number. To guess it put \"guess <num>\", to stop put \"admit\"."
                          gameLoop {number = n})
          pure ()
