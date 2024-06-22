open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

open import Notation.Variables

module Misc where

StableΣ : {A : Type ℓ} {P : A → Type ℓ'} →
  Stable A → isProp A → ((a : A) → Stable (P a)) → Stable (Σ A P)
StableΣ {P = P} As Aprop Ps e =
  let a = (As (λ notA → e (λ (a , _) → notA a))) in
  a ,
  Ps a λ notPa → e (λ (a' , p) → notPa (subst P (Aprop a' a) p))

¬¬map : {A : Type ℓ} {B : Type ℓ'} → (A → B) → NonEmpty A → NonEmpty B
¬¬map f ¬¬A ¬B = ¬¬A (λ a → ¬B (f a))

¬¬in : {A : Type ℓ} → A → ¬ ¬ A
¬¬in z = λ w → w z

