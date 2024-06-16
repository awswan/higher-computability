open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sum
open import StrictlyCounted.Base

open import Encodings.Sum

open import Notation.Variables

module StrictlyCounted.Sum where

instance
  sCounted⊎ : {A : Type ℓ} {B : Type ℓ'} ⦃ ctdA : StrictlyCounted A ⦄
    ⦃ ctdB : StrictlyCounted B ⦄ → StrictlyCounted (A ⊎ B)
  StrictlyCounted.equiv (sCounted⊎ ⦃ ctdA ⦄ ⦃ ctdB ⦄) =
    invEquiv oddEvenEquiv ∙ₑ ⊎-equiv equivA equivB
    where
      equivA = StrictlyCounted.equiv ctdA
      equivB = StrictlyCounted.equiv ctdB
