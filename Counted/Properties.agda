open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection

open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation

open import Dominance.Base

open import StrictlyCounted.Base

open import Counted.Base

open import Notation.ModalOperatorSugar
open import Notation.Variables

module Counted.Properties where

instance
  strictlyCounted→Counted : {X : Type ℓ}
    ⦃ sctdX : StrictlyCounted X ⦄ → Counted X
  Counted.enum (strictlyCounted→Counted ⦃ sctdX ⦄) n =
    return (equivFun (StrictlyCounted.sCtdEquiv sctdX) n)
  Counted.isSurjEnum (strictlyCounted→Counted ⦃ sctdX ⦄) x =
    map (λ (n , p) → n , (tt* , p))
        (isEquiv→isSurjection (snd (StrictlyCounted.sCtdEquiv sctdX)) x)
