open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sum
open import HigherComputability.StrictlyCounted.Base

open import HigherComputability.Encodings.Sum

open import HigherComputability.Notation.Variables

module HigherComputability.StrictlyCounted.Sum where

abstract instance
  sCounted⊎ : {A : Type ℓ} {B : Type ℓ'} ⦃ ctdA : StrictlyCounted A ⦄
    ⦃ ctdB : StrictlyCounted B ⦄ → StrictlyCounted (A ⊎ B)
  StrictlyCounted.sCtdEquiv (sCounted⊎ {A = A} {B = B} ⦃ ctdA ⦄ ⦃ ctdB ⦄) =
    invEquiv oddEvenEquiv ∙ₑ ⊎-equiv sCtdEquiv sCtdEquiv
