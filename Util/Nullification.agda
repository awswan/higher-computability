open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.Nullification.Properties

open import Notation.Variables

module Util.Nullification where

nullFiber : {S : A → Type ℓ} (α : Null S B) → Null S (fiber ∣_∣ α)
nullFiber = elim (λ α → isNull-Null _) λ b → ∣ b , refl ∣
