open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties

open import Cubical.Data.Empty

open import Cubical.HITs.Nullification

open import Notation.Variables

module Types.DoubleNegationSheaves where

DenseProps : (ℓ : Level) → Σ[ P ∈ hProp ℓ ] ¬ ¬ (fst P) → Type ℓ
DenseProps ℓ = fst ∘ fst

∇ : Type ℓ' → Type (ℓ-max ℓ' (ℓ-suc ℓ))
∇ {ℓ = ℓ} = Null (DenseProps ℓ)

Sheaf : Type ℓ' → Type (ℓ-max ℓ' (ℓ-suc ℓ))
Sheaf {ℓ = ℓ} = isNull (DenseProps ℓ)

open isPathSplitEquiv

PropSheaf→Stable : {A : Type ℓ} → isProp A → Sheaf A → Stable A
PropSheaf→Stable {A = A} propA shfA ¬¬A =
  fst (sec (shfA ((A , propA) , ¬¬A))) (λ x → x)

StableProp→Sheaf : {A : Type ℓ'} → Stable A → isProp A → Sheaf {ℓ = ℓ} A
StableProp→Sheaf stableA propA P =
  fromIsEquiv _ (snd (propBiimpl→Equiv propA (isProp→ propA)
    (λ a _ → a) (λ f → stableA (¬¬map f (snd P)))))

_⇓ : {A : Type ℓ'} → ∇ {ℓ = ℓ} A → Type (ℓ-max ℓ' (ℓ-suc ℓ))
α ⇓ = fiber ∣_∣ α
