open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.HITs.Nullification.Base

open import Notation.Variables

module Reducibilities where

-- _≤T_ : {A : Type ℓa} {B : Type ℓb} → (A → Type ℓ) → (B → Type ℓ) →
--   Type (ℓ-max (ℓ-max ℓa ℓ) ℓb)
-- _≤T_ {A = A} P Q = (a : A) → isContr (Null Q (P a))

_≤11_ : {A : Type ℓa} {B : Type ℓb} → (A → Type ℓ) → (B → Type ℓ') →
  Type (ℓ-max (ℓ-max ℓa (ℓ-max ℓ ℓ')) ℓb)
_≤11_ {A = A} {B = B} P Q =
  Σ[ e ∈ A ↪ B ] ((a : A) → P a ≃ Q (fst e a))

_≤m_ : {A : Type ℓa} {B : Type ℓb} → (A → Type ℓ) → (B → Type ℓ') →
  Type (ℓ-max (ℓ-max ℓa (ℓ-max ℓ ℓ')) ℓb)
_≤m_ {A = A} {B = B} P Q = Σ[ f ∈ (A → B) ] ((a : A) → P a ≃ Q (f a))
