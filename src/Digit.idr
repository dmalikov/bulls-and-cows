module Digit

import Data.String.Views
import Data.Vect

%access public export
%default total

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

fromStr : String -> Maybe Digit
fromStr s with (strList s)
  fromStr "" | SNil = Nothing
  fromStr (strCons c rest) | (SCons c _) with (strList rest)
    fromStr (strCons c "") | (SCons c _) | SNil = fromChar c
    fromStr (strCons c (strCons c' _)) | (SCons c _) | (SCons c' _) = Nothing

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

digits : Vect 10 Digit
digits = [D0,D1,D2,D3,D4,D5,D6,D7,D8,D9]
