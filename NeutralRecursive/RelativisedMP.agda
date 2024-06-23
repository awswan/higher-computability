open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import Cubical.Induction.WellFounded
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.HITs.Nullification
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Base
open import Cubical.Data.Sum renaming (rec to ⊎rec)
open import CubicalExtras.Data.Nat.Properties
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

_⇓ : {A : Type ℓ'} → ∇ ℓ'' A → Type (ℓ-max ℓ' (ℓ-suc ℓ''))
α ⇓ = fiber ∣_∣ α

private
  mpInst : ∇ ℓ' ℕ → Type (ℓ-max ℓbase (ℓ-suc ℓ'))
  mpInst ν = ((n : ℕ) → M (Dec (ν ≡ ∣ n ∣))) → M (ν ⇓)

relMarkovsPrinciple₀ : (ν : ∇ ℓ ℕ) → mpInst ν
relMarkovsPrinciple₀ {ℓ = ℓ} = markovInduction step
  where
    step : (ν : ∇ ℓ ℕ) → ((μ : ∇ ℓ ℕ) → fst (isSucc∇ μ ν) → mpInst μ) →
      mpInst ν
    step ν ih dec = do
      (no ¬p) ← dec 0
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

searchUnique : (P : ℕ → Type ℓ)
  (isUnique : (m n : ℕ) → (P m) → (P n) → m ≡ n)
  (dec : (n : ℕ) → M (Dec (P n)))
  (¬¬exists : ¬ ¬ (Σ ℕ P)) → M (Σ ℕ P)
searchUnique {ℓ = ℓ} P isUnique dec ¬¬exists = do
  (n , q) ← relMarkovsPrinciple₀ ν νdec
  no ¬r ← dec n
    where yes r → return (n , r)
  let p = subst lP (sym q) lPν
  return (⊥rec (p ¬r))
  where
    P' : ℕ → Type ℓ
    P' n = ¬ ¬ (P n)

    uniqueP' : isProp (Σ ℕ P')
    uniqueP' (m , p) (n , q) =
      Σ≡Prop (λ _ → isProp→ isProp⊥) (separatedℕ _ _ r)
      where
        r : ¬ ¬ (m ≡ n)
        r = do
          p ← p
          q ← q
          return (isUnique m n p q)

    ¬¬exists' : ¬ ¬ (Σ ℕ P')
    ¬¬exists' = do
      (n , p) ← ¬¬exists
      return (n , (¬¬in p))

    ν : ∇ ℓ ℕ
    ν = hub ((Σ ℕ P' , uniqueP') , ¬¬exists') λ (n , _) → ∣ n ∣

    νValue : (n : ℕ) → P' n → ν ≡ ∣ n ∣
    νValue n p = spoke ((Σ ℕ P' , uniqueP') , ¬¬exists')
      (λ (n , _) → ∣ n ∣) (n , p)

    lP : ∇ _ ℕ → Type ℓ
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

boundedSearch : (P : ℕ → Type ℓ) (dec : (n : ℕ) → M (Dec (P n)))
  (n : ℕ) →
  M ((Σ[ m ∈ Fin n ] leastSuch P (fst m)) ⊎ ((m : Fin n) → ¬ P (fst m)))
boundedSearch P dec zero = return (inr (λ (m , m<0) _ → ¬-<-zero m<0))
boundedSearch P dec (suc n) = do
  inr not<n ← boundedSearch P dec n
    where inl ((m , m<n) , p) → return (inl ((m , (≤-suc m<n)) , p))
  no ¬pn ← dec n
     where yes pn → return
                  (inl ((n , ≤-refl) , (pn , (λ m m<n → not<n (m , m<n)))))
  return (inr (λ (m , m<n) →
          ⊎rec (λ m<n → not<n (m , m<n))
               (λ m≡n → subst (λ z → ¬ (P z)) (sym m≡n) ¬pn)
               (<-split m<n)))


searchFirst : (P : ℕ → Type ℓ)
  (dec : (n : ℕ) → M (Dec (P n)))
  (¬¬exists : ¬ ¬ (Σ ℕ P)) → M (Σ ℕ (leastSuch P))
searchFirst P dec ¬¬exists =
  searchUnique (leastSuch P) leastUnique leastDec'
    λ w → ¬¬exists (λ (n , v) → convertEx w n v)
    where
      leastDec' : (n : ℕ) → M (Dec (leastSuch P n))
      leastDec' n = do
        yes p ← dec n
          where no ¬p → return (no (λ (p , _) → ¬p p))
        inr none< ← boundedSearch P dec n
          where inl ((m , m<n) , p) →
                    return (no (λ (_ , l) → l m m<n (fst p)))
        return (yes (p , (λ m m<n → none< (m , m<n))))

      convertEx : ¬ (Σ ℕ (leastSuch P)) → (n : ℕ) → ¬ (P n)
      convertEx z = WFI.induction <-wellfounded λ n w v → z (n , (v , w))

search : (P : ℕ → Type ℓ)
  (dec : (n : ℕ) → M (Dec (P n)))
  (¬¬exists : ¬ ¬ (Σ ℕ P)) → M (Σ ℕ P)
search P dec ¬¬exists =
  searchFirst P dec ¬¬exists >>= λ (n , (p , _)) → return (n , p)
