open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.HITs.Nullification
open import Cubical.Data.Nat
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Sigma.Properties
open import Axioms.MarkovInduction
open import Types.NablaNat

open import Types.DoubleNegationSheaves

open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.DoubleNegation
open import Notation.Variables

module NeutralRecursive.RelativisedMP
  {ℓbase : Level}
  (M : {ℓ : Level} → Type ℓ → Type (ℓ-max ℓbase ℓ))
  ⦃ _ : ModalOperator ℓbase M ⦄
  where

--searchFirst : (P : ℕ → Type ℓ) → {!!}

_⇓ : {A : Type ℓ'} → ∇ ℓ'' A → Type (ℓ-max ℓ' (ℓ-suc ℓ''))
α ⇓ = fiber ∣_∣ α

private
  mpInst : ∇ ℓ' ℕ → Type (ℓ-max ℓbase (ℓ-suc ℓ'))
  mpInst ν = ((n : ℕ) → M (Dec (ν ≡ ∣ n ∣))) → M (ν ⇓)

relMarkovsPrinciple₀ : (ν : ∇ ℓ ℕ) → mpInst ν
relMarkovsPrinciple₀ {ℓ = ℓ} = markovInduction step
  where
    step : (ν : ∇ ℓ ℕ) → ((μ : ∇ ℓ ℕ) → fst (isSucc∇ μ ν) → mpInst μ) → mpInst ν
    step ν ih dec = do
      (no ¬p) ← dec 0 -- dec 0
        where yes p → return (0 , sym p)
      let (μ , is) = nonZeroToPredecessor ν ¬p
      (m , x) ← ih μ is (convertDec μ is)
      return ((suc m) , (sym (definedToSuc is m (sym x))))
      where
        convertDec : (μ : ∇ ℓ ℕ)
          (is : fst (isSucc∇ μ ν)) → (m : ℕ) →
          (M (Dec (μ ≡ ∣ m ∣)))
        convertDec μ is m = do
          yes p ← dec (suc m)
            where no ¬p → return (no (λ q → ¬p (definedToSuc is m q)))
          return (yes (definedToPred is m p))

searchUnique : (P : ℕ → Type ℓ) (isUnique : (m n : ℕ) → (P m) → (P n) → m ≡ n)
  (¬¬exists : ¬ ¬ (Σ ℕ P)) (dec : (n : ℕ) → M (Dec (P n))) → M (Σ ℕ P)
searchUnique {ℓ = ℓ} P isUnique ¬¬exists dec = do
  (n , q) ← relMarkovsPrinciple₀ ν νdec
  no ¬r ← dec n
    where yes r → return (n , r)
  let p = subst lP (sym q) lPν
  return (⊥rec (p ¬r))
  where
    P' : ℕ → Type ℓ
    P' n = ¬ ¬ (P n)

    uniqueP' : isProp (Σ ℕ P')
    uniqueP' (m , p) (n , q) = Σ≡Prop (λ _ → isProp→ isProp⊥) (separatedℕ _ _ r)
      where
        r : ¬ ¬ (m ≡ n)
        r = do
          p ← p
          q ← q
          return (isUnique m n p q)
    
    ν : ∇ ℓ ℕ
    ν = hub (((Σ[ n ∈ ℕ ] ¬ ¬ (P n)) , uniqueP') , ¬¬map (λ (n , p) → n , (¬¬in p)) ¬¬exists)
            λ (n , _) → ∣ n ∣

    νValue : (n : ℕ) → P' n → ν ≡ ∣ n ∣
    νValue n p = spoke ((((Σ[ n ∈ ℕ ] ¬ ¬ (P n)) , uniqueP') , ¬¬map (λ (n , p) → n , (¬¬in p)) ¬¬exists)) (λ (n , _) → ∣ n ∣) (n , p)

    lP : ∇ ℓ ℕ → Type ℓ
    lP = fst ∘ rec (isNullNullTypes (DenseProps ℓ)  (snd ∘ fst) {ℓ})
      (λ n → (P' n) ,
             (StableProp→Sheaf ℓ Stable¬ (isProp→ isProp⊥)))

    lPν : lP ν
    lPν = snd

    νdec : (n : ℕ) → M (Dec (ν ≡ ∣ n ∣))
    νdec n = do
      no ¬p ← dec n
        where yes p → return (yes (νValue n (¬¬in p)))
      return (no (λ q → subst lP q lPν ¬p))

