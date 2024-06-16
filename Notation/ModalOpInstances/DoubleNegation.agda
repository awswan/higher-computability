open import Cubical.Core.Everything
open import Cubical.Relation.Nullary

open import Notation.ModalOperatorSugar

module Notation.ModalOpInstances.DoubleNegation where

instance
  ¬¬-modal : {ℓa ℓb : Level} → ModalOperator ℓ-zero ℓa ℓb (λ {ℓ} A → ¬ ¬ A)
  ¬¬-modal = record { bind = λ nna f nb → nna (λ a → f a nb) }
