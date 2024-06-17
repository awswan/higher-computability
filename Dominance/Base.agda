open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Functions.Embedding

open import Partiality.Base

open import Notation.Variables

module Dominance.Base where

record PreDominance : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    Idx : Type ℓ
    P : Idx → Type ℓ'
    isPropP : (d : Idx) → isProp (P d)

record ∂Pred (D : PreDominance {ℓ = ℓ} {ℓ' = ℓ'}) (X : Type ℓ'') :
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  field
    d : PreDominance.Idx D
    ξ : PreDominance.P D d → X

instance
  ∂PredToPartial : {D : PreDominance {ℓ = ℓ} {ℓ' = ℓ'}} {X : Type ℓ''} →
    CoercesToPartial X (∂Pred D X) ℓ'
  ∂.domain (CoercesToPartial.getPartial (∂PredToPartial {D = D} {X = X}) s) =
    PreDominance.P D (∂Pred.d s)
  ∂.isPropDomain (CoercesToPartial.getPartial (∂PredToPartial {D = D} {X = X}) s) =
    PreDominance.isPropP D (∂Pred.d s)
  ∂.value (CoercesToPartial.getPartial (∂PredToPartial {D = D} {X = X}) s) =
    ∂Pred.ξ s

record Dominance : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    pred : PreDominance {ℓ = ℓ} {ℓ' = ℓ'}
  open PreDominance pred
  field
    isEmbeddingP : isEmbedding P
    unit : Idx
    isInhUnit : P unit
    ΣLift : (x : Idx) → (P x → Idx) → Idx
    ΣLiftIsΣ : {x : Idx} {Q : P x → Idx} → P (ΣLift x Q) ≡ Σ (P x) (P ∘ Q)

ι : (dom : Dominance {ℓ = ℓ} {ℓ' = ℓ'}) {X : Type ℓ''} →
  X → ∂Pred (Dominance.pred dom) X
∂Pred.d (ι dom x) = Dominance.unit dom
∂Pred.ξ (ι dom x) _ = x

ιdefd : (dom : Dominance {ℓ = ℓ} {ℓ' = ℓ'}) {X : Type ℓ''} →
  (x : X) → ι dom x ↓
ιdefd dom x = Dominance.isInhUnit dom

_⊑_ : {ℓA ℓS ℓS' : Level} {A : Type ℓA} {S : Type ℓS}
  ⦃ ctp : CoercesToPartial A S ℓ ⦄ → (α : S) →
  {S' : Type ℓS'} ⦃ ctp' : CoercesToPartial A S' ℓ' ⦄ →
  (β : S') →
  Type (ℓ-max ℓA (ℓ-max ℓ ℓ'))
α ⊑ β = α ↓= a ⇒ (β ↓= b & (b ≡ a))
