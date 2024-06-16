open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.Replacement

open import Cubical.Displayed.Universe

open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Partiality.Base

open import Dominance.Base

open import Types.NatInf

open import Notation.Variables
open import Notation.CoercesToType
open import Notation.ModalOperatorSugar

-- open import Misc

module Dominance.Rosolini where

PreRos : PreDominance {ℓ = ℓ-zero} {ℓ' = ℓ-zero}
PreDominance.Idx PreRos = Replacement (𝒮-Univ ℓ-zero) λ (α : ℕ∞) → ⟨ α ⟩
PreDominance.P PreRos = unrep (𝒮-Univ ℓ-zero) λ (α : ℕ∞) → ⟨ α ⟩
PreDominance.isPropP PreRos =
  elimProp (𝒮-Univ ℓ-zero) (λ (α : ℕ∞) → ⟨ α ⟩)
           (λ _ → isPropIsProp) ℕ∞.unique



Ros : Dominance
Dominance.pred Ros = PreRos
Dominance.isEmbeddingP Ros =
  isEmbeddingUnrep (𝒮-Univ ℓ-zero) (λ (α : ℕ∞) → ⟨ α ⟩)
Dominance.ΣLift Ros = {!!}
Dominance.ΣLiftIsΣ Ros = {!!}
