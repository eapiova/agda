{-# OPTIONS --cubical-compatible -Werror #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

suc-inj : {n m : Nat} -> suc n ≡ suc m -> n ≡ m
suc-inj refl = refl
