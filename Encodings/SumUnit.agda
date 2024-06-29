open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sum.Base

module Encodings.SumUnit where

ℕSumUnitIso : Iso ℕ (ℕ ⊎ Unit)
Iso.fun ℕSumUnitIso zero = inr tt
Iso.fun ℕSumUnitIso (suc n) = inl n
Iso.inv ℕSumUnitIso (inl n) = suc n
Iso.inv ℕSumUnitIso (inr _) = 0
Iso.leftInv ℕSumUnitIso zero = refl
Iso.leftInv ℕSumUnitIso (suc n) = refl
Iso.rightInv ℕSumUnitIso (inl n) = refl
Iso.rightInv ℕSumUnitIso (inr _) = refl

ℕSumUnitEquiv : ℕ ≃ ℕ ⊎ Unit
ℕSumUnitEquiv = isoToEquiv ℕSumUnitIso
