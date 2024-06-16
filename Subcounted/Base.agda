open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation

open import Partiality.Base
open import Dominance.Base
open import Dominance.DoubleNegation

open import Notation.Variables

module Subcounted.Base where

record Subcounted (ℓ' : Level) (X : Type ℓ)
  : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    subEnum : ℕ → ∂¬¬ ℓ' X
    allSubctd : (x : X) → ∥ Σ[ n ∈ ℕ ] subEnum n ↓= y & (y ≡ x) ∥₁
