open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.Nullification.Properties

open import Notation.Variables

module CubicalExtras.HITs.Nullification.Properties where

generatorsConnected : {A : Type ℓa} (S : A → Type ℓ) →
  (a : A) → isContr (Null S (S a))
generatorsConnected S a = (hub a ∣_∣) ,
  elim (λ _ → isNull≡ (isNull-Null S)) (spoke a ∣_∣)

nullMap : {A : Type ℓa} (S : A → Type ℓ) →
  {X : Type ℓ'} {Y : Type ℓ''} → (X → Y) → Null S X → Null S Y
nullMap S f ∣ x ∣ = ∣ f x ∣
nullMap S f (hub α g) = hub α (λ z → nullMap S f (g z))
nullMap S f (spoke α g s i) = spoke α (λ z → nullMap S f (g z)) s i
nullMap S f (≡hub p i) = ≡hub (λ z j → nullMap S f (p z j)) i
nullMap S f (≡spoke p s i i₁) = ≡spoke (λ z j → nullMap S f (p z j)) s i i₁

nullPreservesIso : {A : Type ℓa} (S : A → Type ℓ) → {X : Type ℓ'} →
  {Y : Type ℓ''} → Iso X Y → Iso (Null S X) (Null S Y)
Iso.fun (nullPreservesIso S e) = nullMap S (Iso.fun e)
Iso.inv (nullPreservesIso S e) = nullMap S (Iso.inv e)
Iso.leftInv (nullPreservesIso S e) =
  elim (λ _ → isNull≡ (isNull-Null S)) (λ x → cong ∣_∣ (Iso.leftInv e x))
Iso.rightInv (nullPreservesIso S e) =
  elim (λ _ → isNull≡ (isNull-Null S)) (λ y → cong ∣_∣ (Iso.rightInv e y))

nullPreservesEquiv : {A : Type ℓa} (S : A → Type ℓ) → {X : Type ℓ'} →
  {Y : Type ℓ''} → X ≃ Y → Null S X ≃ Null S Y
nullPreservesEquiv S {X = X} {Y = Y} e = isoToEquiv (nullPreservesIso S (equivToIso e))
