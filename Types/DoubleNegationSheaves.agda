open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary

open import Cubical.HITs.Nullification

open import Notation.Variables

module Types.DoubleNegationSheaves where

∇ : (ℓ' : Level) → Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ'))
∇ ℓ' = Null {A = Σ[ P ∈ hProp ℓ' ] ¬ ¬ (fst P)} (fst ∘ fst)
