open import HigherComputability.StrictlyCounted.Base
open import Cubical.Data.Nat
open import Cubical.Foundations.Equiv

module HigherComputability.StrictlyCounted.Nat where

instance
  sCountedℕ : StrictlyCounted ℕ
  StrictlyCounted.sCtdEquiv sCountedℕ = idEquiv ℕ
