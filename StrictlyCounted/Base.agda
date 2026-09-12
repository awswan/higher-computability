open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat

open import Notation.Variables

module StrictlyCounted.Base where

record StrictlyCounted (X : Type ℓ) : Type ℓ where
  field
    sCtdEquiv : ℕ ≃ X

open StrictlyCounted ⦃...⦄ public

sEnum : {X : Type ℓ} ⦃ _ : StrictlyCounted X ⦄ → ℕ → X
sEnum = equivFun sCtdEquiv
