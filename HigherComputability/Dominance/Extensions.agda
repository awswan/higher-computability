open import HigherComputability.Dominance.Base
open import HigherComputability.Notation.Variables

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty

module HigherComputability.Dominance.Extensions where

record ContainsEmpty (P : PreDominance ℓ ℓ') : Type ℓ' where
  open PreDominance P
  field
    containsEmpty : inDom ⊥*


module _ {P : PreDominance ℓ ℓ'} ⦃ ce : ContainsEmpty P ⦄ {A : Type ℓ''} where
  open ContainsEmpty ce
  undefined : ∂ P A
  undefined ↓ = ⊥*
  domainInD undefined = containsEmpty
