{-# OPTIONS --cubical-compatible -Werror #-}

data I : Set where
  i : I

data D : I -> Set where
  c : D i

f : (x : I) -> D x -> D x
f i c = c
