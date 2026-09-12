open import Cubical.Foundations.Prelude
open import HigherComputability.Notation.Variables

module HigherComputability.Notation.CoercesToType where

record CoercesToType (X : Type ℓ) (ℓ' : Level) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    getType : X → Type ℓ'

⟨_⟩ : {X : Type ℓ} ⦃ hut : CoercesToType X ℓ' ⦄ → X → Type ℓ'
⟨_⟩ ⦃ hut ⦄ x = CoercesToType.getType hut x
