open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import Cubical.Induction.WellFounded
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.HITs.Nullification renaming (rec to nullRec)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Bool.Base
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Base
open import Cubical.Data.Sum renaming (rec to ⊎rec)
open import CubicalExtras.Data.Nat.Properties
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Sigma.Properties
open import Axioms.MarkovInduction

open import Counted.Base
open import Dominance.Base
open import Dominance.Bool

open import Types.DoubleNegationSheaves
open import Types.NablaNat
open import Types.NablaZero
open import Types.PropNegNeg

open import Notation.CoercesToType
open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.DoubleNegation
open import Notation.Variables

module NeutralRecursive.MarkovsPrinciple
  {ℓbase : Level}
  (M : {ℓ : Level} → Type ℓ → Type (ℓ-max ℓbase ℓ))
  ⦃ _ : ModalOperator ℓbase M ⦄
  ⦃ _ : {ℓ' : Level} → MarkovInduction {ℓ = ℓ'} ⦄
  where

private
  mpInst : ∇₀ {ℓ = ℓ} ℕ → Type (ℓ-max ℓbase ℓ)
  mpInst ν = ((n : ℕ) → M (Dec (⟨ ∇₀.isThis ν n ⟩))) → M (ν ⇓₀)

locatedToDefined : (ν : ∇₀ {ℓ = ℓ} ℕ) → mpInst ν
locatedToDefined {ℓ = ℓ} = WFI.induction markovInduction step
  where
    step : (ν : ∇₀ ℕ) → ((μ : ∇₀ ℕ) → ⟨ isSuc∇₀ μ ν ⟩ → mpInst μ) →
      mpInst ν
    step ν ih dec = do
      (no ¬p) ← dec 0
        where yes p → return (0 , p)
      let (μ , is) = nonZeroToPredecessor ν ¬p
      (m , x) ← ih μ is λ m → convertDec μ is m
      return ((suc m) , definedToSuc μ ν is m x)
      where
        convertDec : (μ : ∇₀ ℕ)
          (is : ⟨ isSuc∇₀ μ ν ⟩) → (m : ℕ) →
          (M (Dec (⟨ ∇₀.isThis μ m ⟩)))
        convertDec μ is m = do
          yes p ← dec (suc m)
            where no ¬p → return (no λ q → ¬p (definedToSuc μ ν is m q))
          return (yes (definedToPred μ ν is m p))

searchUnique : (P : ℕ → Type ℓ)
  (isUnique : (m n : ℕ) → (P m) → (P n) → m ≡ n)
  (dec : (n : ℕ) → M (Dec (P n)))
  (¬¬exists : ¬ ¬ (Σ ℕ P)) → M (Σ ℕ P)
searchUnique {ℓ = ℓ} P isUnique dec ¬¬exists = do
  (n , q) ← locatedToDefined ν νdec
  no ¬r ← dec n
    where yes r → return (n , r)
  return (⊥rec (q ¬r))
  where
    ν : ∇₀ ℕ
    hProp¬¬.P (∇₀.isThis ν n) = ¬ ¬ (P n)
    hProp¬¬.isPropP (∇₀.isThis ν n) = isProp¬ (¬ P n)
    hProp¬¬.StableP (∇₀.isThis ν n) = Stable¬
    ∇₀.wellDefd ν n n' x x' = do
      p ← x
      p' ← x'
      return (isUnique n n' p p')
    ∇₀.almostInh ν = ¬¬map (λ (n , p) → n , (¬¬in p)) ¬¬exists

    νdec : (n : ℕ) → M (Dec ⟨ ∇₀.isThis ν n ⟩)
    νdec n = do
      no ¬p ← dec n
        where yes p → return (yes (¬¬in p))
      return (no (λ x → x ¬p))

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
  searchUnique (leastSuch P) leastUnique leastDecM
    λ w → ¬¬exists (λ (n , v) → convertEx w n v)
    where
      leastDecM : (n : ℕ) → M (Dec (leastSuch P n))
      leastDecM n = do
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

searchCtd : {A : Type ℓa} ⦃ _ : Counted A ⦄
  (P : A → Type ℓ) (dec : (a : A) → M (Dec (P a)))
  (¬¬exists : NonEmpty (Σ A P)) → M (Σ A P)
searchCtd P dec ¬¬exists = lemma >>= λ (n , (enumn↓ , p)) → return ((value (enum n) enumn↓) , p)
  where
    dec' : (n : ℕ) (x : PreDominance.inDom BoolPred (enum n ↓)) → M (Dec (enum n ↓= a & P a))
    dec' n (false , e) = return (no (λ (enumn↓ , _) →  invEq e enumn↓))
    dec' n (true , e) = do
      no ¬p ← dec (value (enum n) enumn↓)
        where yes p → return (yes (enumn↓ , p))
      return (no (λ (enumn↓' , p) →
        ¬p (subst (P ∘ value (enum n)) (isPropDomain (enum n) enumn↓' enumn↓) p)))
      
      where
        enumn↓ = equivFun e tt
    
    lemma : M (Σ[ n ∈ ℕ ] enum n ↓= a & P a)
    lemma = search (λ n → enum n ↓= a & P a)
                   (λ n → dec' n (domainInD (enum n)))
                   (¬¬exists >>= λ (a , p) →
                     rec (isProp¬ _) (λ (n , q) →
                       ¬¬in (n , (map-snd (λ r → subst P (sym r) p) q))) (isSurjEnum a))
