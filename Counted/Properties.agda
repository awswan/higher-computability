open import Cubical.Core.Everything
open import Cubical.Functions.Surjection

open import Cubical.Data.Nat

open import StrictlyCounted.Base

open import Counted.Base

open import Notation.Variables

module Counted.Properties where

strictlyCounted→Counted : (X : Type ℓ)
  ⦃ sctdX : StrictlyCounted X ⦄ → Counted X
Counted.enum (strictlyCounted→Counted X ⦃ sctdX ⦄) =
  equivFun (StrictlyCounted.equiv sctdX)
Counted.isSurjEnum (strictlyCounted→Counted X ⦃ sctdX ⦄) =
  isEquiv→isSurjection (snd (StrictlyCounted.equiv sctdX))
