open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.HITs.PropositionalTruncation
open import Dominance.Base
open import Dominance.Bool

open import Notation.Variables

module Counted.Base where

record Counted (X : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ-zero)) where
  field
    enum : ℕ → ∂Bool {ℓ' = ℓ-zero} X
    isSurjEnum : (x : X) → ∥ (Σ[ n ∈ ℕ ] (enum n ↓= y & y ≡ x)) ∥₁

open Counted ⦃...⦄ public
