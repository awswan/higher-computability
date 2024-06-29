open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties
open import Axioms.ComputableChoice

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import StrictlyCounted.Base
open import Subcounted.Base

open import Dominance.Base
open import Dominance.NatInf
open import Dominance.DoubleNegation

open import Types.NatInf
open import Types.PropNegNeg

open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.PropositionalTruncation
open import Notation.ModalOpInstances.DoubleNegation
open import Notation.CoercesToType
open import Notation.Variables

module FirstKleene.SubcountableChoice
  ( mp : (α : ℕ∞) → Stable ⟨ α ⟩ )
  where

φ⟨_⇒_⟩ : 
  (A : Type ℓa) (B : Type ℓb) ⦃ _ : StrictlyCounted A ⦄ →
  ⦃ _ : Subcounted ℓ B ⦄
  (n : ℕ) → A → ∂¬¬ ℓ B
φ⟨ A ⇒ B ⟩ e a = ∂ℕ∞→∂¬¬ mp (φ e (invEq sCtdEquiv a)) >>= subEnum

subCountedChoice :   {ℓA : Level} {A : Type ℓA} ⦃ sctdA : StrictlyCounted A ⦄
  {ℓB ℓscb : Level} {B : Type ℓB} ⦃ subctdB : Subcounted ℓB B ⦄ →
  (R : A → B → hProp¬¬ ℓ) →
  ((a : A) → NonEmpty (Σ[ b ∈ B ] ⟨ R a b ⟩) → ∥ Σ[ b ∈ B ] ⟨ R a b ⟩ ∥₁) →
  ∥ Σ[ e ∈ ℕ ] ((a : A) → NonEmpty (Σ[ b ∈ B ] ⟨ R a b ⟩) →
                   φ⟨ A ⇒ B ⟩ e a ↓= b & ⟨ R a b ⟩) ∥₁

subCountedChoice {ℓ = ℓ} {A = A} {ℓB = ℓB} {B = B} R Rtotal = do
  (e , eWorks) ← ComputableChoice R' Rtotal'
  return (e , λ a ¬¬b →
    reformatR'→R e a (eWorks (invEq sCtdEquiv a)
      (¬¬b >>= λ (b , r) →
        rec (isProp¬ _)
            (λ (m , (sm↓ , p)) →
              ¬¬in (m , (sm↓ , subst2 (λ a b → ⟨ R a b ⟩)
                                      (sym (secEq sCtdEquiv a)) (sym p) r)))
            (allSubctd b))))
  where
    R' : ℕ → ℕ → hProp¬¬ (ℓ-max ℓ ℓB)
    hProp¬¬.P (R' n m) = subEnum m ↓= b & ⟨ R (equivFun sCtdEquiv n) b ⟩
    hProp¬¬.isPropP (R' n m) =
      isPropΣ (isPropDomain (subEnum m))
              (λ d → hProp¬¬.isPropP (R (equivFun sCtdEquiv n) (value (subEnum m) d)))
    hProp¬¬.StableP (R' n m) =
      isDefinedAndStable (subEnum m) λ b → hProp¬¬.StableP (R _ b)

    Rtotal' : (n : ℕ) → NonEmpty (Σ[ m ∈ ℕ ] ⟨ R' n m ⟩ ) →
      ∥ Σ[ m ∈ ℕ ] ⟨ R' n m ⟩ ∥₁
    Rtotal' n ¬¬m = do
      (b , r) ← Rtotal (equivFun sCtdEquiv n)
                 (¬¬map (λ (m , (sm↓ , r)) → value (subEnum m) sm↓ , r) ¬¬m)
      (m , (sm↓ , p)) ← allSubctd b
      return (m , (sm↓ , subst (λ b → ⟨ R _ b ⟩) (sym p) r))

    reformatR'→R : (e : ℕ) (a : A) →
      (φ e (invEq sCtdEquiv a) ↓= m & ⟨ R' (invEq sCtdEquiv a) m ⟩) →
      φ⟨ A ⇒ B ⟩ e a ↓= b & ⟨ R a b ⟩
    reformatR'→R e a (φea↓ , (sm↓ , r)) = ((lift φea↓) , sm↓) ,
      (subst (λ a → ⟨ R a (value (subEnum _) sm↓) ⟩) (secEq sCtdEquiv a) r)
