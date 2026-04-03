{-# OPTIONS --cubical-compatible -Werror #-}

open import Agda.Builtin.Nat

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

lookup : {A : Set} {n : Nat} -> Fin n -> Vec A n -> A
lookup zero (x :: xs) = x
lookup (suc i) (x :: xs) = lookup i xs
