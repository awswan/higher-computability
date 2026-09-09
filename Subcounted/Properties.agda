open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation

open import Counted.Base
open import Subcounted.Base
open import Dominance.Base
open import Dominance.Bool
open import Dominance.DoubleNegation

open import Notation.Variables

module Subcounted.Properties where

counted→subCounted : (X : Type ℓ) ⦃ ctdX : Counted X ⦄ → Subcounted ℓ' X
Subcounted.subEnum (counted→subCounted {ℓ = ℓ} {ℓ' = ℓ'} X ⦃ ctdX ⦄) n =
  ∂Bool→∂¬¬ (enum n)
Subcounted.allSubctd (counted→subCounted {ℓ' = ℓ'} X ⦃ ctdX ⦄) x =
  map (λ (n , (d , p)) → n , (lift d , p)) (isSurjEnum x)
