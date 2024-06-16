open import Cubical.Foundations.Prelude
open import Cubical.Functions.Surjection
open import Cubical.Data.Nat
open import Counted.Base

open import Notation.Variables

module Counted.FromCovered where

countedFromCovered : {B : Type ℓ'} {A : Type ℓ} ⦃ ctdA : Counted A ⦄ →
  A ↠ B → Counted B
countedFromCovered {B = B} ⦃ ctdA ⦄ s =
  record { enum = fst e ; isSurjEnum = snd e }
  where
    e : ℕ ↠ B
    e = compSurjection ((Counted.enum ctdA) , (Counted.isSurjEnum ctdA)) s
