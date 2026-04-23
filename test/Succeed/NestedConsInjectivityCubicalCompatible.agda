{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch #-}

-- Regression test: the pattern (outer cons-forcing Solution +
-- DInjectivity + cons-valued hidden args) previously crashed the
-- typechecker with an internal __IMPOSSIBLE__ at LeftInverse.hs:533
-- (compose-time substitution-shape mismatch). See
-- eval/prefix-nested-cons-discovery.md.
--
-- Under patched: must typecheck (clause is punted via CantCompose).

open import Agda.Builtin.Bool
open import Agda.Builtin.List

-- Mono-sorted version to keep the test minimal.
data Prefix {A : Set}
  (R : A → A → Set)
  : List A → List A → Set where
  []  : ∀ {bs} → Prefix R [] bs
  _∷_ : ∀ {a b as bs}
    → R a b → Prefix R as bs → Prefix R (a ∷ as) (b ∷ bs)

-- Minimal trigger. The outer `{xs = x ∷ xs}` forces a list cons on an
-- implicit index; the subsequent `(_ ∷ _)` triggers DInjectivity on
-- Prefix's `_∷_` whose hidden args are cons-valued.
is-cons : {A : Set} {xs ys : List A}
  → Prefix (λ _ _ → A) xs ys → Bool
is-cons {xs = []}     _       = false
is-cons {xs = x ∷ xs} (_ ∷ _) = true
