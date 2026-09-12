open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary

open import HigherComputability.Axioms.MarkovInduction

open import HigherComputability.Counted.Base

open import HigherComputability.Notation.ModalOpInstances.Identity
open import HigherComputability.Notation.Variables

module HigherComputability.NeutralRecursive.CountedMP where

open import HigherComputability.NeutralRecursive.ModalMarkovsPrinciple
  {ℓbase = ℓ-zero} (λ {ℓ} → idfun (Type ℓ))

countedMP : ⦃ _ : MarkovInduction ℓ' ⦄ {A : Type ℓ} ⦃ ctdA : Counted A ⦄
  (P : A → Type ℓ')
  (dec : (a : A) → Dec (P a)) → Stable (Σ[ a ∈ A ] P a)
countedMP P dec = searchCtd P dec
