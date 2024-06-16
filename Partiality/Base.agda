open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Base

open import Cubical.Reflection.StrictEquiv

open import Notation.Variables

open import Misc

module Partiality.Base where

variable
  ℓ''' ℓa ℓs : Level

record ∂ (ℓ' : Level) (X : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    domain : Type ℓ'
    isPropDomain : isProp domain
    value : domain → X

record CoercesToPartial (A : Type ℓ) (S : Type ℓ') (ℓ'' : Level) :
  Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓ'')) ℓ') where
  field
    getPartial : S → ∂ ℓ'' A

instance
  ∂CoercesToPartial : {A : Type ℓ} → CoercesToPartial A (∂ ℓ' A) ℓ'
  CoercesToPartial.getPartial ∂CoercesToPartial α = α

module _ {A : Type ℓa} {S : Type ℓs} ⦃ ctp : CoercesToPartial A S ℓ ⦄ where
  open CoercesToPartial ctp
  
  _↓ : S → Type ℓ
  _↓ α = ∂.domain (CoercesToPartial.getPartial ctp α) 

  eval : (α : S) → α ↓ → A
  eval α d = ∂.value (getPartial α) d

  isPropDefined : {α : S} → isProp (α ↓)
  isPropDefined {α} = ∂.isPropDomain (getPartial α)

  evalUnique : {α : S} → (d d' : α ↓) → eval α d ≡ eval α d'
  evalUnique {α = α} d d' = cong (eval α) (isPropDefined d d')

  isDefinedAnd : (α : S) → (Z : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
  isDefinedAnd α Z = Σ[ d ∈ α ↓ ] Z (eval α d)

  isDefinedImplies : (α : S) → (Z : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
  isDefinedImplies α Z = (d : α ↓) → Z (eval α d)

  syntax isDefinedAnd α (λ x → Z) = α ↓= x & Z
  syntax isDefinedImplies α (λ x → Z) = α ↓= x ⇒ Z

  ↓=&hLevel : (n : HLevel) (α : S) {Z : A → Type ℓ'} →
    ((a : A) → isOfHLevel (suc n) (Z a)) →
    isOfHLevel (suc n) (α ↓= a & Z a)
  ↓=&hLevel n α l =
    isOfHLevelΣ _ (isProp→isOfHLevelSuc n isPropDefined)
                λ d → l (eval α d)
