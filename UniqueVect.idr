module UniqueVect

import Data.Vect

%default total

data UniqueVect : Vect n a -> Type where
  UVEmpty : UniqueVect []
  UVSingleton : UniqueVect [x]
  UVCons : Not (Elem x xs) -> UniqueVect xs -> UniqueVect (x :: xs)

-- toUnique : Vect n a -> Maybe (UniqueVect (Vect n a))
