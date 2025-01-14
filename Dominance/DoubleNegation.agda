open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Types.PropNegNeg

open import Dominance.Base

open import Notation.Variables
open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.DoubleNegation


module Dominance.DoubleNegation where

open PreDominance

¬¬PreDom : (ℓ : Level) → PreDominance ℓ ℓ
inDom (¬¬PreDom ℓ) P = isProp P × Stable P
onlyProps (¬¬PreDom ℓ) P e = fst e
containsUnit (¬¬PreDom ℓ) = isPropUnit* , (λ _ → tt*)
Σclosed (¬¬PreDom ℓ) (isPropP , StableP) stablePropQ =
  (isPropΣ isPropP λ p → fst (stablePropQ p)) ,
  StableΣ StableP isPropP λ p → snd (stablePropQ p)

∂¬¬ : (ℓ' : Level) → Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ'))
∂¬¬ ℓ' = ∂ (¬¬PreDom ℓ')

∂¬¬domainStable : {A : Type ℓ} (α : ∂¬¬ ℓ' A) → (Stable (α ↓))
∂¬¬domainStable α = snd (domainInD α)

isDefinedAndStable : {A : Type ℓ} (α : ∂¬¬ ℓ' A) {Z : A → Type ℓ''} →
  (zstable : (a : A) → Stable (Z a)) → Stable (α ↓= a & Z a)
isDefinedAndStable α zstable = StableΣ (∂¬¬domainStable α)
  (isPropDomain α) λ d → zstable (value α d)
