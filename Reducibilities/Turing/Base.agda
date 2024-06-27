open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Bool.Base
open import Cubical.HITs.Nullification.Base

open import Types.DoubleNegationSheaves
open import Types.PropNegNeg

open import Reducibilities

open import Notation.Variables
open import Notation.CoercesToType

module Reducibilities.Turing.Base where

_≤T_ : {A : Type ℓa} {B : Type ℓb} → (A → Type ℓ) → (B → Type ℓ') →
  Type (ℓ-max (ℓ-max ℓa (ℓ-max ℓ ℓ')) ℓb)
_≤T_ {A = A} P Q = (a : A) → isContr (Null Q (P a))

_≡T_ : {A : Type ℓa} {B : Type ℓb} → (A → Type ℓ) → (B → Type ℓ') →
  Type (ℓ-max (ℓ-max ℓa (ℓ-max ℓ ℓ')) ℓb)
P ≡T Q = (P ≤T Q) × (Q ≤T P)

private variable
  A : Type ℓa

[_] : {A : Type ℓa} {B : Type ℓb} (χ : A → ∇ {ℓ = ℓ} B) → A →
  Type (ℓ-max ℓb (ℓ-suc ℓ))
[ χ ] a = χ a ⇓

-- ≡11→T : (P : A → Type ℓ) {B : Type ℓb} (Q : B → Type ℓ') → (P ≤11 Q) → (P ≡T Q)

≤m→≤T : (P : A → Type ℓ) {B : Type ℓb} (Q : B → Type ℓ') → (P ≤m Q) → (P ≤T Q)
≤m→≤T P Q r = {!!}

Dec→oracle : (P : A → hProp¬¬ ℓ) →
  Σ[ χ ∈ (A → ∇ {ℓ = ℓ} Bool) ] ((λ a → Dec ⟨ P a ⟩) ≡T [ χ ])
Dec→oracle {A = A}  {ℓ = ℓ}  P = (λ a → fst (pointwise a)) ,
  (≤m→≤T (λ a → Dec ⟨ P a ⟩) [ fst ∘ pointwise ] ((idfun A) , (snd ∘ pointwise))) ,
  ≤m→≤T [ fst ∘ pointwise ] ((λ a → Dec ⟨ P a ⟩))
        ((idfun A) , (invEquiv ∘ snd ∘ pointwise))
  where
    pointwise : (a : A) → Σ[ β ∈ ∇ {ℓ = ℓ} Bool ] (Dec ⟨ P a ⟩ ≃ (β ⇓))
    pointwise a = Dec⇓ {ℓ = ℓ} (P a)
