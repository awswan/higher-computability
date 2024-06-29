open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat.Base
open import StrictlyCounted.Base

open import Notation.Variables

module StrictlyCounted.Properties where

sCtdFromEquiv : {A : Type ℓa} {B : Type ℓb} ⦃ _ : StrictlyCounted B ⦄
  (e : A ≃ B) → StrictlyCounted A
StrictlyCounted.sCtdEquiv (sCtdFromEquiv e) = sCtdEquiv ∙ₑ invEquiv e
