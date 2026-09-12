open import HigherComputability.Counted.Base
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation
open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.Bool

open import HigherComputability.Notation.ModalOperatorSugar

module HigherComputability.Counted.Nat where

instance
  countedℕ : Counted ℕ
  Counted.enum countedℕ n = return n
  Counted.isSurjEnum countedℕ n = ∣ n , (tt* , refl) ∣₁
