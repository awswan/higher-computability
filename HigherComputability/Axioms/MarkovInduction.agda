open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded
open import Cubical.Data.Nat.Base

open import HigherComputability.Types.NablaNat
open import HigherComputability.Types.PropNegNeg

open import HigherComputability.Notation.ModalOperatorSugar
open import HigherComputability.Notation.CoercesToType

open import HigherComputability.Types.DoubleNegationSheaves

module HigherComputability.Axioms.MarkovInduction where

record MarkovInduction (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    markovInduction : WellFounded {ℓ' = ℓ} (λ μ ν →  ⟨ isSuc∇₀ μ ν ⟩)

open MarkovInduction ⦃...⦄ public
