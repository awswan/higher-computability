open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation

open import HigherComputability.Subcounted.Base
open import HigherComputability.Subcounted.Properties

open import HigherComputability.Counted.Nat

open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.DoubleNegation

open import HigherComputability.Notation.Variables

module HigherComputability.Subcounted.Nat where

opaque instance
  subCountedℕ : Subcounted ℓ ℕ
  subCountedℕ = counted→subCounted ℕ
