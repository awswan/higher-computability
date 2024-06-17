open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Base
open import Cubical.Functions.Surjection

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Counted.Base

open import Encodings.Product

open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.PropositionalTruncation
open import Notation.Variables

module Counted.Sigma where

instance
  countedΣ : {A : Type ℓ} {B : A → Type ℓ'} ⦃ ctdA : Counted A ⦄
    ⦃ ctdB : {a : A} → Counted (B a) ⦄ → Counted (Σ A B)
  countedΣ {A = A} {B} ⦃ ctdA ⦄ ⦃ ctdB ⦄ =
    record { enum = fst e ; isSurjEnum = snd e }
    where
      fromℕ×ℕ : (ℕ × ℕ) → Σ A B
      fst (fromℕ×ℕ (n , m)) =
        (Counted.enum ctdA n)
      snd (fromℕ×ℕ (n , m)) = Counted.enum (ctdB {Counted.enum ctdA n}) m
      
      fromℕ×ℕsurj : isSurjection fromℕ×ℕ
      fromℕ×ℕsurj (a , b) = do
        (n , p) ← Counted.isSurjEnum ctdA a
        (m , q) ← Counted.isSurjEnum (ctdB {a}) b
        ∣ (n , m) ,
          cong (λ a → a , Counted.enum (ctdB {a}) m) p ∙
          ΣPathP (refl , q) ∣₁
      
      e : ℕ ↠ Σ A B
      e = compSurjection
        ((fst (invEquiv ℕPairEquiv)) ,
          isEquiv→isSurjection (snd (invEquiv ℕPairEquiv)))
        (fromℕ×ℕ , fromℕ×ℕsurj)
