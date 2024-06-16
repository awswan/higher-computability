open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Functions.Surjection

open import Notation.Variables

module Counted.Base where

record Counted (X : Type ℓ) : Type ℓ where
  field
    enum : ℕ → X
    isSurjEnum : isSurjection enum

open Counted ⦃...⦄ public
