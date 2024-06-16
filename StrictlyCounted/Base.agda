open import Cubical.Core.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat

open import Notation.Variables

module StrictlyCounted.Base where

record StrictlyCounted (X : Type ℓ) : Type ℓ where
  field
    equiv : ℕ ≃ X

instance
  sCountedℕ : StrictlyCounted ℕ
  StrictlyCounted.equiv sCountedℕ = idEquiv ℕ
