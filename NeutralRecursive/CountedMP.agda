open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat.Base
open import Cubical.Data.Empty.Properties
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.HITs.PropositionalTruncation
open import NeutralRecursive.MarkovsPrinciple
open import Counted.Base

open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.DoubleNegation
open import Notation.Variables

module NeutralRecursive.CountedMP where

countedMP : {A : Type ℓ} ⦃ ctdA : Counted A ⦄ (P : A → Type ℓ')
  (dec : (a : A) → Dec (P a)) → Stable (Σ[ a ∈ A ] P a)
countedMP P dec ¬¬ap = (enum n) , Pn
  where
    P' : ℕ → Type _
    P' = P ∘ enum

    dec' = dec ∘ enum

    ¬¬ap' : ¬ ¬ (Σ[ n ∈ ℕ ] P' n)
    ¬¬ap' = do
      (a , p) ← ¬¬ap
      (n , q) ← rec (isProp→ isProp⊥) (λ x → ¬¬in x) (isSurjEnum a)
      ¬¬in (n , (subst P (sym q) p))

    mpInstance = markovsPrinciple P' dec' ¬¬ap'
    n = fst mpInstance
    Pn = snd mpInstance
