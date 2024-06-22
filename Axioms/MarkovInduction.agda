open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Induction.WellFounded
open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.Nullification.Properties
open import Cubical.HITs.Nullification.Topological
open import Cubical.Data.Nat hiding (elim)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty renaming (rec to ⊥rec) hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

open import CubicalExtras.Data.Nat.Properties

open import Types.NablaNat

open import Misc

open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.Nullification

open import Types.DoubleNegationSheaves

module Axioms.MarkovInduction {ℓ : Level} where

postulate
  wellFounded∇Suc : WellFounded {ℓ' = ℓ} (λ μ ν → fst (isSucc∇ μ ν))
  
markovInduction = WFI.induction wellFounded∇Suc

markovsPrinciple₀ : (ν : ∇ ℓ ℕ) → ((n : ℕ) → Dec (ν ≡ ∣ n ∣)) →
  Σ[ n ∈ ℕ ] ν ≡ ∣ n ∣
markovsPrinciple₀ = markovInduction step
  where
    P : ∇ ℓ ℕ → Type (ℓ-suc ℓ)
    P ν = ((n : ℕ) → Dec (ν ≡ ∣ n ∣)) → Σ[ n ∈ ℕ ] ν ≡ ∣ n ∣

    stepIf≠0 : (ν : ∇ ℓ ℕ) → ((μ : ∇ ℓ ℕ) → fst (isSucc∇ μ ν) → P μ) →
      ¬ ν ≡ ∣ 0 ∣ → P ν
    stepIf≠0 ν ih ν≢0 dec =
      let (m , p) = ih μ μisPred dec' in (suc m) , (definedToSuc μisPred m p)
      where
        μ = fst (nonZeroToPredecessor ν ν≢0)
        μisPred = snd (nonZeroToPredecessor ν ν≢0)

        dec' : (m : ℕ) → Dec (μ ≡ ∣ m ∣)
        dec' m = decRec (λ p → yes (definedToPred μisPred m p))
                        (λ ¬p → no (λ q → ¬p (definedToSuc μisPred m q))) (dec (suc m))

    step : (ν : ∇ ℓ ℕ) → ((μ : ∇ ℓ ℕ) → fst (isSucc∇ μ ν) → P μ) → P ν
    step ν ih dec = decRec (λ p → 0 , p) (λ ¬p → stepIf≠0 ν ih ¬p dec) (dec 0)

markovsPrinciple : (P : ℕ → Type ℓ) → ((n : ℕ) → Dec (P n)) →
  ¬ ¬ (Σ[ n ∈ ℕ ] P n) → Σ[ n ∈ ℕ ] P n
markovsPrinciple P dec ¬¬np = m , Pm
  where
    P' = leastSuch λ n → ¬ ¬ (P n)

    dec¬¬ : (n : ℕ) → Dec (¬ ¬ (P n))
    dec¬¬ n = decRec (λ p → yes (¬¬in p)) (λ ¬p → no (¬¬in ¬p)) (dec n)

    leastWitnesses = Σ[ n ∈ ℕ ] P' n

    open isPathSplitEquiv

    μ : ∇ ℓ ℕ
    μ = hub ((leastWitnesses , (isPropLeastWitnesses (λ _ → isProp→ isProp⊥))) ,
            ¬¬map (λ (n , p) → leastExists dec¬¬ n (¬¬in p)) ¬¬np)
            (∣_∣ ∘ fst)

    μValue : (m : ℕ) → P' m → μ ≡ ∣ m ∣
    μValue m p = spoke _ (∣_∣ ∘ fst) (m , p)

    {- A key feature of topological modalities is that we can define types by
       recursion in the universe. We make use of that here. -}
    lP : ∇ ℓ ℕ → Type ℓ
    lP = fst ∘ rec (isNullNullTypes (DenseProps ℓ) (snd ∘ fst) {ℓ = ℓ})
                   λ n → (P' n) ,
                       (StableProp→Sheaf ℓ (StableLeastSuch (λ _ → Stable¬) n)
                         (isPropLeastSuch (λ _ → isProp→ isProp⊥) n))
    lPμ : lP μ
    lPμ = snd

    μdec : (m : ℕ) → Dec (μ ≡ ∣ m ∣)
    μdec m with leastDec dec¬¬ m
    ... | yes p = yes (spoke _ _ (m , p))
    ... | no ¬p = no
      (λ q → ¬p (subst lP q lPμ))

    m = fst (markovsPrinciple₀ μ μdec)
    p = snd (markovsPrinciple₀ μ μdec)

    Pm : P m
    Pm = Dec→Stable (dec m) (fst (subst lP p lPμ))
