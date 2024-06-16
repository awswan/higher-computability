open import Counted.Base
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation

module Counted.Nat where

instance
  countedℕ : Counted ℕ
  Counted.enum countedℕ n = n
  Counted.isSurjEnum countedℕ n = ∣ n , refl ∣₁
