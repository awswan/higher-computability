open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary

open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Unit

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

ΣBool : (b : Bool) (c : (Bool→Type b) → Bool) → Bool
ΣBool false c = false
ΣBool true c = c tt

ΣBoolΣIso : {b : Bool} {c : (Bool→Type b) → Bool} →
  Iso (Bool→Type (ΣBool b c)) (Σ[ z ∈ Bool→Type b ] Bool→Type (c z))

Iso.fun (ΣBoolΣIso {true}) x = tt , x
Iso.inv (ΣBoolΣIso {true}) x = snd x
Iso.leftInv (ΣBoolΣIso {true}) _ = refl
Iso.rightInv (ΣBoolΣIso {true}) _ = refl

ΣBool≃Σ : {b : Bool} {c : (Bool→Type b) → Bool} →
  (Bool→Type (ΣBool b c)) ≃ (Σ[ z ∈ Bool→Type b ] Bool→Type (c z))
ΣBool≃Σ = isoToEquiv ΣBoolΣIso
