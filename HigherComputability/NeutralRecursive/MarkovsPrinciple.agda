open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.Nat.Base
open import Cubical.Data.Bool

open import HigherComputability.Axioms.MarkovInduction

open import HigherComputability.Types.NatInf

open import HigherComputability.Notation.Variables
open import HigherComputability.Notation.CoercesToType
open import HigherComputability.Notation.ModalOperatorSugar
open import HigherComputability.Notation.ModalOpInstances.Identity

module HigherComputability.NeutralRecursive.MarkovsPrinciple where

open import HigherComputability.NeutralRecursive.ModalMarkovsPrinciple {ℓbase = ℓ-zero} (λ {ℓ} → idfun (Type ℓ))

markovsPrinciple :
  ⦃ _ : MarkovInduction ℓ ⦄
  (P : ℕ → Type ℓ) →
  (dec : (n : ℕ) → Dec (P n)) →
  Stable (Σ ℕ P)

markovsPrinciple = search

Stable⟨ℕ→Bool⟩ : ⦃ _ : MarkovInduction ℓ-zero ⦄ → (α : ℕ → Bool) → Stable ⟨ α ⟩
Stable⟨ℕ→Bool⟩ α =
  markovsPrinciple (λ n → Bool→Type (α n)) λ n → DecBool→Type

Stable⟨ℕ∞⟩ : ⦃ _ : MarkovInduction ℓ-zero ⦄ (α : ℕ∞) → Stable ⟨ α ⟩
Stable⟨ℕ∞⟩ α = Stable⟨ℕ→Bool⟩ (ℕ∞.f α)
