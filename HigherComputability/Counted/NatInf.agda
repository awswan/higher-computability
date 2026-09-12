open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import HigherComputability.Counted.Base
open import HigherComputability.Counted.FromCovered
open import HigherComputability.Counted.Nat
open import HigherComputability.Counted.Sigma

open import HigherComputability.Axioms.ComputableChoice

open import HigherComputability.Types.NatInf

module HigherComputability.Counted.NatInf where


instance
  Countedℕ∞ : Counted ℕ∞
  Countedℕ∞ = countedFromCovered (ℕ × ℕ) {!!}
    where
