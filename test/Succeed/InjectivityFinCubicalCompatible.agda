{-# OPTIONS --cubical-compatible -Werror #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc  : {n : Nat} -> Fin n -> Fin (suc n)

-- Direct Fin.suc injectivity: requires the DInjectivity retract to handle
-- an indexed constructor whose visible field depends on the hidden prefix.
fin-suc-inj : {n : Nat} {i j : Fin n} -> Fin.suc i ≡ Fin.suc j -> i ≡ j
fin-suc-inj refl = refl
