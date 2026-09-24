open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.Extensions
open import HigherComputability.Notation.Variables
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

module HigherComputability.Dominance.AllProps where

open PreDominance
  
allProps : (ℓ : Level) → PreDominance ℓ ℓ
inDom (allProps ℓ) X = isProp X
onlyProps (allProps ℓ) X z = z
containsUnit (allProps ℓ) = isPropUnit*
Σclosed (allProps ℓ) = isPropΣ

instance
  allPropsContainsEmpty : ContainsEmpty (allProps ℓ)
  ContainsEmpty.containsEmpty allPropsContainsEmpty = isProp⊥*

∂* : (ℓ : Level) → Type ℓ' → Type (ℓ-max ℓ' (ℓ-suc ℓ))
∂* ℓ = ∂ (allProps ℓ)
