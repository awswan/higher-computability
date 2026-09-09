open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.HITs.PropositionalTruncation.Base
open import Notation.Variables

module Util.DoubleNegation where

¬¬map : {A : Type ℓ} {B : Type ℓ'} → (A → B) → NonEmpty A → NonEmpty B
¬¬map f ¬¬A ¬B = ¬¬A (λ a → ¬B (f a))

¬¬in : {A : Type ℓ} → A → ¬ ¬ A
¬¬in z = λ w → w z

-- Factors through Populated, following
-- Cubical.Relation.Nullary.Properties
∥∥₁→NonEmpty : {A : Type ℓ} → ∥ A ∥₁ → NonEmpty A
∥∥₁→NonEmpty x = notEmptyPopulated (populatedBy x)

equivPreservesStable : {A : Type ℓ} {B : Type ℓ'} → A ≃ B → Stable A → Stable B
equivPreservesStable e stabA ¬¬b = equivFun e (stabA (¬¬map (invEq e) ¬¬b))
