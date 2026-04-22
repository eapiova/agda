{-# OPTIONS --cubical-compatible -Werror #-}

-- Mirrors the user manual example at
-- doc/user-manual/language/cubical.lagda.rst:800-886 using a user-defined
-- `Eq` data type (not Agda.Builtin.Equality). The DInjectivity retract
-- must handle the constructor-injectivity implicit in `sucInjEq reflEq = reflEq`.

open import Agda.Builtin.Nat

data Eq {A : Set} (x : A) : A -> Set where
  reflEq : Eq x x

sucInjEq : {n k : Nat} -> Eq (suc n) (suc k) -> Eq n k
sucInjEq reflEq = reflEq
