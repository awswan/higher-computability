open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary.Base
open import Dominance.Base
open import Dominance.DoubleNegation

open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Fin

open import Axioms.MarkovInduction
open import NeutralRecursive.MarkovsPrinciple

open import Types.NatInf

open import Notation.CoercesToType
open import Notation.Variables

open import Types.NatInf

open import Util.DoubleNegation

module Dominance.NatInf where

open PreDominance

ℕ∞Pred : PreDominance ℓ-zero ℓ-zero
inDom ℕ∞Pred P = Σ[ α ∈ ℕ∞ ] P ≃ ⟨ α ⟩
onlyProps ℕ∞Pred P (α , e) =
  isOfHLevelRespectEquiv 1 (invEquiv e) (ℕ∞.unique α)
containsUnit ℕ∞Pred = ℕ→ℕ∞ 0 , invEquiv (isContr→≃Unit*
  (inhProp→isContr (ℕ→ℕ∞Ptd 0) (ℕ∞.unique (ℕ→ℕ∞ 0))))
Σclosed ℕ∞Pred {P = P} {Q = Q} (α , e) d =
  ℕ∞Σ α (λ x → fst (d (invEq e x))) ,
  (Σ P Q
    ≃⟨ Σ-cong-equiv-snd (λ p → snd (d p)) ⟩
  Σ[ p ∈ P ] ⟨ fst (d p) ⟩
    ≃⟨ invEquiv (Σ-cong-equiv-fst (invEquiv e)) ⟩
  Σ[ x ∈ ⟨ α ⟩ ] ⟨ fst (d (invEq e x)) ⟩
    ≃⟨ invEquiv (ℕ∞Σ≃ α (λ x → fst (d (invEq e x)))) ⟩
  ⟨ ℕ∞Σ α (λ x → fst (d (invEq e x))) ⟩ ■)

∂ℕ∞ : Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
∂ℕ∞ = ∂ ℕ∞Pred

∂ℕ∞→∂¬¬ : ⦃ _ : MarkovInduction ℓ-zero ⦄ {A : Type ℓa} → ∂ℕ∞ A → ∂¬¬ ℓ A
∂._↓ (∂ℕ∞→∂¬¬ α) = Lift (α ↓)
∂.domainInD (∂ℕ∞→∂¬¬ {ℓ = ℓ} ⦃ mi ⦄ α) = isOfHLevelLift 1 (isPropDomain α) ,
  λ x → lift (equivPreservesStable (invEquiv (snd (domainInD α)))
                              (Stable⟨ℕ∞⟩ (fst (domainInD α)))
                              (¬¬map lower x))
∂.value (∂ℕ∞→∂¬¬ α) x = value α (lower x)
