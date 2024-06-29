open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Base
open import Cubical.Functions.Surjection

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Counted.Base

open import Dominance.Base
open import Dominance.Bool

open import Encodings.Product

open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.PropositionalTruncation
open import Notation.Variables

module Counted.Sigma where

abstract instance
  countedΣ : {A : Type ℓ} {B : A → Type ℓ'} ⦃ ctdA : Counted A ⦄
    ⦃ ctdB : {a : A} → Counted (B a) ⦄ → Counted (Σ A B)

  countedΣ {A = A} {B = B} =
    record { enum = enumFromPair ∘ invEq ℕPairEquiv ;
             isSurjEnum = λ ab → map (equivFun (reindexFibre ab)) (surjFromPair ab)}
    where
      enumFromPair : ℕ × ℕ → ∂Bool {ℓ' = ℓ-zero} (Σ A B)
      ∂._↓ (enumFromPair (na , nb)) = enum na ↓= a & enum {X = B a} nb ↓
      ∂.domainInD (enumFromPair (na , nb)) =
        Σclosed (domainInD (enum {X = A} na))
          λ d → domainInD (enum {X = B _} nb) 
        where
          open PreDominance BoolPred
      ∂.value (enumFromPair (na , nb)) (da , db) =
        (value (enum na) da) , value (enum nb) db

      surjFromPair : (ab : Σ A B) →
        ∥ Σ[ nanb ∈ ℕ × ℕ ] (enumFromPair nanb ↓= p & p ≡ ab) ∥₁
      surjFromPair (a , b) = do
        (na , (da , pa)) ← isSurjEnum a
        (nb , (db , pb)) ← isSurjEnum b
        let (nb' , (db' , p)) = transport
                 (λ i → Σ[ nb ∈ ℕ ] (enum {X = B (pa (~ i))} nb ↓= b' & (pa (~ i) , b') ≡ (a , b)))
                 (nb , db , (ΣPathP (refl , pb)))
        return ((na , nb') , (da , db') , p)

      reindexFibre : (ab : Σ A B) →
        (Σ[ nanb ∈ ℕ × ℕ ] (enumFromPair nanb ↓= p & p ≡ ab)) ≃
          (Σ[ n ∈ ℕ ] (enumFromPair (invEq ℕPairEquiv n) ↓= p & p ≡ ab))
      reindexFibre ab = invEquiv (Σ-cong-equiv-fst (invEquiv ℕPairEquiv))
