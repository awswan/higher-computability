open import HigherComputability.Dominance.Base
open import HigherComputability.Notation.Variables

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.Sum renaming (rec to ⊎-rec; elim to ⊎-elim)
open import Cubical.HITs.PropositionalTruncation

module HigherComputability.Dominance.Extensions where

record ContainsEmpty (P : PreDominance ℓ ℓ') : Type ℓ' where
  open PreDominance P
  field
    containsEmpty : inDom ⊥*


undefined : {P : PreDominance ℓ ℓ'} ⦃ ce : ContainsEmpty P ⦄ {A : Type ℓ''}
  → ∂ P A
undefined ↓ = ⊥*
domainInD (undefined ⦃ ce ⦄) = containsEmpty
  where
    open ContainsEmpty ce

record SupportsUnionAndPick (P : PreDominance ℓ ℓ') : Type (ℓ-max (ℓ-suc ℓ) ℓ') where
  open PreDominance P
  field
    unionInDom : {A B : Type ℓ} → inDom A → inDom B → inDom ∥ A ⊎ B ∥₁
    pick : {A B : Type ℓ} (inA : inDom A) (inB : inDom B) → ∥ A ⊎ B ∥₁ → A ⊎ B

module _ {P : PreDominance ℓ ℓ'} ⦃ pu : SupportsUnionAndPick P ⦄ {A : Type ℓ''} where
  open SupportsUnionAndPick pu

  _⊔_ : ∂ P A → ∂ P A → ∂ P A
  (x ⊔ y) ↓ = ∥ (x ↓) ⊎ (y ↓) ∥₁
  domainInD (x ⊔ y) = unionInDom (x .domainInD) (y .domainInD)
  value (x ⊔ y) z = ⊎-rec (x .value) (y .value) (pick (x .domainInD) (y .domainInD) z)

  ⊔rec : (Z : A → Type ℓ''') {x y : ∂ P A} → isDefinedImplies x Z → isDefinedImplies y Z
    → isDefinedImplies (x ⊔ y) Z
  ⊔rec Z {x} {y} f g w = ⊎-elim {C = λ v → Z (⊎-rec (x .value) (y .value) v)}
    f g (pick (x .domainInD) (y .domainInD) w)
