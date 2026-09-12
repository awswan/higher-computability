open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation

open import HigherComputability.Counted.Base
open import HigherComputability.Subcounted.Base
open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.Bool
open import HigherComputability.Dominance.DoubleNegation

open import HigherComputability.Notation.Variables

module HigherComputability.Subcounted.Properties where

counted→subCounted : (X : Type ℓ) ⦃ ctdX : Counted X ⦄ → Subcounted ℓ' X
Subcounted.subEnum (counted→subCounted {ℓ = ℓ} {ℓ' = ℓ'} X ⦃ ctdX ⦄) n =
  ∂Bool→∂¬¬ (enum n)
Subcounted.allSubctd (counted→subCounted {ℓ' = ℓ'} X ⦃ ctdX ⦄) x =
  map (λ (n , (d , p)) → n , (lift d , p)) (isSurjEnum x)
