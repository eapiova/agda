{-# OPTIONS --cubical-compatible -Werror #-}

open import Agda.Builtin.Nat

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

head : {A : Set} {n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x

tail : {A : Set} {n : Nat} -> Vec A (suc n) -> Vec A n
tail (x :: xs) = xs
