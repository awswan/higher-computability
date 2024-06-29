open import StrictlyCounted.Base
open import Cubical.Data.Nat
open import Cubical.Foundations.Equiv

module StrictlyCounted.Nat where

instance
  sCountedℕ : StrictlyCounted ℕ
  StrictlyCounted.sCtdEquiv sCountedℕ = idEquiv ℕ
