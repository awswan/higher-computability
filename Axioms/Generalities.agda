open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Empty.Properties
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma

open import Dominance.Base
open import Dominance.DoubleNegation
open import Dominance.NatInf

open import Types.PropNegNeg
open import Types.NatInf

open import Axioms.MarkovInduction

open import NeutralRecursive.MarkovsPrinciple

open import Notation.Variables
open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.PropositionalTruncation
open import Notation.CoercesToType

module Axioms.Generalities
  {A : Type ℓa}
  {ℓ : Level}
  (sepA : Separated A)
  (s : A → A → ∂ℕ∞ A)
  (dense : (R : A → A → hProp¬¬ (ℓ-max ℓa ℓ)) →
    ((a : A) → NonEmpty (Σ[ b ∈ A ] ⟨ R a b ⟩) → ∥ Σ[ b ∈ A ] ⟨ R a b ⟩ ∥₁) →
    ∥ Σ[ e ∈ A ] ((a : A) → NonEmpty (Σ[ b ∈ A ] ⟨ R a b ⟩) → s e a ↓= b & ⟨ R a b ⟩) ∥₁)
  where

totalVersion : (R : A → A → hProp¬¬ (ℓ-max ℓa ℓ)) →
  ((a : A) → ∥ Σ[ b ∈ A ] ⟨ R a b ⟩ ∥₁) →
  ∥ Σ[ e ∈ A ] ((a : A) → s e a ↓= b & ⟨ R a b ⟩) ∥₁
totalVersion R total = do
  (b , bWorks) ← dense R (λ a _ → total a)
  return (b , (λ a → bWorks a (rec (isProp→ isProp⊥) ¬¬in (total a))))

private
  setA = Separated→isSet sepA

functionalVersion : (f : A → ∂¬¬ ℓ A) →
  ∥ Σ[ e ∈ A ] f ⊑ s e ∥₁
functionalVersion f = do
  (b , bWorks) ← dense R Rtotal
  return (b , (λ a fa↓ →
    map-snd (λ (fa↓' , p) → p ∙ cong (value (f a)) (isPropDomain (f a) fa↓' fa↓))
            (bWorks a (¬¬in (value (f a) fa↓ , fa↓ , refl)))))
  where
    R : A → A → hProp¬¬ _
    hProp¬¬.P (R a c) = f a ↓= b & c ≡ b
    hProp¬¬.isPropP (R a c) = isPropΣ (isPropDomain (f a)) (λ _ → setA _ _)
    hProp¬¬.StableP (R a c) = isDefinedAndStable (f a) (λ b → sepA c b)

    Rtotal : (a : A) → NonEmpty (Σ[ b ∈ A ] ⟨ R a b ⟩) → ∥ Σ[ b ∈ A ] ⟨ R a b ⟩ ∥₁
    Rtotal a ¬¬ex = ∣ (value (f a) fa↓) , (fa↓ , refl) ∣₁
      where
        fa↓ : f a ↓
        fa↓ = ∂¬¬domainStable (f a) (¬¬map (fst ∘ snd) ¬¬ex)

module WithMP ⦃ _ : MarkovInduction ℓ-zero ⦄ where
  twoArgFunVersion :  (f : A → A → ∂¬¬ ℓ A) →
    ∥ Σ[ e ∈ A ] ((a : A) → s e a ↓= e' & f a ⊑ s e') ∥₁
  twoArgFunVersion f = totalVersion R Rtotal
    where
      R : A → A → hProp¬¬ _
      hProp¬¬.P (R a e') = f a ⊑ s e'
      hProp¬¬.isPropP (R a e') =
        isPropΠ (λ b → isPropΠ (λ _ → isPropΣ (isPropDomain (s e' b)) λ _ → setA _ _))
      hProp¬¬.StableP (R a e') =
        StableΠ (λ b → StableΠ
          (λ x → StableΣ
            (equivPresStable (invEquiv (snd (domainInD (s e' b))))
              (Stable⟨ℕ∞⟩ (fst (domainInD (s e' b))))) (isPropDomain (s e' b)) λ _ → sepA _ _))
  
      Rtotal : (a : A) → ∥ Σ[ e' ∈ A ] ⟨ R a e' ⟩ ∥₁
      Rtotal a = functionalVersion (f a)

  fixedPoint : (f : A → A → ∂¬¬ ℓ A) → ∥ (Σ[ e ∈ A ] (f e ⊑ s e)) ∥₁
  fixedPoint f = do
    (e , eWorks) ← twoArgFunVersion g
    let (ee↓ , eWorks') = eWorks e
    let e₀ = value (s e e) ee↓
    return (e₀ , λ b fe₀b↓ → eWorks' b ((lift ee↓) , fe₀b↓))
    where
      g : A → A → ∂¬¬ _ A
      g a b = ∂ℕ∞→∂¬¬ (s a a) >>= λ c → f c b
