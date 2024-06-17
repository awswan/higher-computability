open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Counted.Base
open import Counted.FromCovered
open import Counted.Nat
open import Counted.Sigma

open import Axioms.ComputableChoice

open import Types.NatInf

module Counted.NatInf where


instance
  Countedℕ∞ : Counted ℕ∞
  Countedℕ∞ = countedFromCovered (ℕ × ℕ) {!!}
    where
