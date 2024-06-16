open import Cubical.Core.Everything
open import Dominance.Base

open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Fin

open import Types.NatInf

open import Notation.CoercesToType
open import Notation.Variables

module Dominance.NatInf where

ℕPred : PreDominance
PreDominance.Idx ℕPred = ℕ∞
PreDominance.P ℕPred α = ⟨ α ⟩
PreDominance.isPropP ℕPred α = ℕ∞.unique α

∂ℕ∞ : Type ℓ → Type ℓ
∂ℕ∞ = ∂Pred ℕPred

-- withinSteps : {X : Type ℓ} → ∂ℕ∞ X → ℕ → Maybe X
-- withinSteps ξ k = {!!}
