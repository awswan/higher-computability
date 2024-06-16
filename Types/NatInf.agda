open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Notation.CoercesToType

module Types.NatInf where

instance
  hitsOne : CoercesToType (ℕ → Bool) ℓ-zero
  CoercesToType.getType hitsOne f = Σ[ n ∈ ℕ ] Bool→Type (f n)

record ℕ∞ : Type where
  field
    f : ℕ → Bool
    unique : isProp ⟨ f ⟩

instance
  hitsOne' : CoercesToType ℕ∞ ℓ-zero
  CoercesToType.getType hitsOne' α = ⟨ ℕ∞.f α ⟩
