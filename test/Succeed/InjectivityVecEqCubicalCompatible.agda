{-# OPTIONS --cubical-compatible -Werror #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

vcons-inj1
  : {A : Set} {n : Nat} {x y : A} {xs ys : Vec A n}
  -> (x :: xs) ≡ (y :: ys)
  -> x ≡ y
vcons-inj1 refl = refl

vcons-inj2
  : {A : Set} {n : Nat} {x y : A} {xs ys : Vec A n}
  -> (x :: xs) ≡ (y :: ys)
  -> xs ≡ ys
vcons-inj2 refl = refl

map : {A B : Set} {n : Nat} -> (A -> B) -> Vec A n -> Vec B n
map f [] = []
map f (x :: xs) = f x :: map f xs
