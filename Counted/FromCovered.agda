open import Cubical.Foundations.Prelude
open import Cubical.Functions.Surjection
open import Cubical.Data.Nat
open import Dominance.Bool
open import Dominance.Base
open import Counted.Base

open import Notation.ModalOperatorSugar
open import Notation.Variables

module Counted.FromCovered where

countedFromCovered : {B : Type ℓ'} (A : Type ℓ) ⦃ ctdA : Counted A ⦄ →
  A ↠ B → Counted B
Counted.enum (countedFromCovered {B = B} A ⦃ ctdA ⦄ s) n =
  {!enum ⦃ ctdA ⦄ ?!} >>= {!!}
