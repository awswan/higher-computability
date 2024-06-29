open import Counted.Base
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation
open import Dominance.Base
open import Dominance.Bool

open import Notation.ModalOperatorSugar

module Counted.Nat where

instance
  countedℕ : Counted ℕ
  Counted.enum countedℕ n = return n
  Counted.isSurjEnum countedℕ n = ∣ n , (tt* , refl) ∣₁
