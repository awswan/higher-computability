open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import StrictlyCounted.Base

open import Encodings.Product

open import Notation.Variables

module StrictlyCounted.Sigma where

instance
  sCountedΣ : {A : Type ℓ} {B : A → Type ℓ'} ⦃ ctdA : StrictlyCounted A ⦄
    ⦃ ctdB : {a : A} → StrictlyCounted (B a) ⦄ → StrictlyCounted (Σ A B)
  StrictlyCounted.equiv (sCountedΣ {A = A} {B} ⦃ ctdA ⦄ ⦃ ctdB ⦄) =
    invEquiv ℕPairEquiv ∙ₑ
      Σ-cong-equiv equivA (λ n → equivB (equivFun equivA n))
    where
      equivA = StrictlyCounted.equiv ctdA
      equivB = λ (a : A) → StrictlyCounted.equiv (ctdB {a})
