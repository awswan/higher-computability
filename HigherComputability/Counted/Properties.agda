open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection

open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation

open import HigherComputability.Dominance.Base

open import HigherComputability.StrictlyCounted.Base

open import HigherComputability.Counted.Base

open import HigherComputability.Notation.ModalOperatorSugar
open import HigherComputability.Notation.Variables

module HigherComputability.Counted.Properties where

instance
  strictlyCounted→Counted : {X : Type ℓ}
    ⦃ sctdX : StrictlyCounted X ⦄ → Counted X
  Counted.enum (strictlyCounted→Counted ⦃ sctdX ⦄) n =
    return (equivFun (StrictlyCounted.sCtdEquiv sctdX) n)
  Counted.isSurjEnum (strictlyCounted→Counted ⦃ sctdX ⦄) x =
    map (λ (n , p) → n , (tt* , p))
        (isEquiv→isSurjection (snd (StrictlyCounted.sCtdEquiv sctdX)) x)
