open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sum
open import StrictlyCounted.Base

open import Encodings.Sum

open import Notation.Variables

module StrictlyCounted.Sum where

abstract instance
  sCounted⊎ : {A : Type ℓ} {B : Type ℓ'} ⦃ ctdA : StrictlyCounted A ⦄
    ⦃ ctdB : StrictlyCounted B ⦄ → StrictlyCounted (A ⊎ B)
  StrictlyCounted.sCtdEquiv (sCounted⊎ {A = A} {B = B} ⦃ ctdA ⦄ ⦃ ctdB ⦄) =
    invEquiv oddEvenEquiv ∙ₑ ⊎-equiv sCtdEquiv sCtdEquiv
