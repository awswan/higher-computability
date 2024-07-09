open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary.Base

open import Cubical.Data.Nat.Base
open import Cubical.Data.Bool

open import Axioms.MarkovInduction

open import Types.NatInf

open import Notation.Variables
open import Notation.CoercesToType
open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.Identity

module NeutralRecursive.MarkovsPrinciple where

open import NeutralRecursive.ModalMarkovsPrinciple {ℓbase = ℓ-zero} (λ {ℓ} → idfun (Type ℓ))

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
