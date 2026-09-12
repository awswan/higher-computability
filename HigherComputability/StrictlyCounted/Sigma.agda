open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma
open import HigherComputability.StrictlyCounted.Base

open import HigherComputability.Encodings.Product

open import HigherComputability.Notation.Variables

module HigherComputability.StrictlyCounted.Sigma where

abstract instance
  sCountedΣ : {A : Type ℓ} {B : A → Type ℓ'} ⦃ _ : StrictlyCounted A ⦄
    ⦃ _ : {a : A} → StrictlyCounted (B a) ⦄ → StrictlyCounted (Σ A B)
  StrictlyCounted.sCtdEquiv sCountedΣ =
    invEquiv ℕPairEquiv ∙ₑ
      Σ-cong-equiv sCtdEquiv (λ n → sCtdEquiv)
