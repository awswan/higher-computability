open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base
open import Notation.Variables

module Util.DoubleNegation where

¬¬map : {A : Type ℓ} {B : Type ℓ'} → (A → B) → NonEmpty A → NonEmpty B
¬¬map f ¬¬A ¬B = ¬¬A (λ a → ¬B (f a))

¬¬in : {A : Type ℓ} → A → ¬ ¬ A
¬¬in z = λ w → w z
