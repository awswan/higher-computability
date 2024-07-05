open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded
open import Cubical.Data.Nat.Base

open import Types.NablaNat
open import Types.PropNegNeg

open import Notation.ModalOperatorSugar
open import Notation.CoercesToType

open import Types.DoubleNegationSheaves

module Axioms.MarkovInduction {ℓ : Level} where

record MarkovInduction : Type (ℓ-suc ℓ) where
  field
    markovInduction : WellFounded {ℓ' = ℓ} (λ μ ν →  ⟨ isSuc∇₀ μ ν ⟩)

open MarkovInduction ⦃...⦄ public
