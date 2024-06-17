open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation

open import Subcounted.Base
open import Subcounted.Properties

open import Counted.Nat

open import Partiality.Base
open import Dominance.Base
open import Dominance.DoubleNegation

open import Notation.Variables

module Subcounted.Nat where

opaque instance
  subCountedℕ : Subcounted ℓ ℕ
  subCountedℕ = counted→subCounted ℕ
