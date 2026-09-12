open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation

open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.DoubleNegation

open import HigherComputability.Notation.Variables

module HigherComputability.Subcounted.Base where

record Subcounted (ℓ' : Level) (X : Type ℓ)
  : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    subEnum : ℕ → ∂¬¬ ℓ' X
    allSubctd : (x : X) → ∥ Σ[ n ∈ ℕ ] (subEnum n ↓= y & (y ≡ x)) ∥₁

open Subcounted ⦃...⦄ public
