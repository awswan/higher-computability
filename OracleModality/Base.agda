open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary

open import Cubical.HITs.Nullification
open import Types.DoubleNegationSheaves

open import Notation.Variables

module OracleModality.Base where


◯[_] : {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} (χ : A → ∇ {ℓ = ℓ} B) →
  Type ℓ' → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓa) ℓb)
◯[ χ ] = Null (λ a → χ a ⇓)
