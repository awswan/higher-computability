open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

module CubicalExtras.Data.Bool.Properties where

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
