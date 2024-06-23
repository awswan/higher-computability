open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

open import Notation.ModalOperatorSugar

module Notation.ModalOpInstances.DoubleNegation where

open ModalOperator

instance
  ¬¬modal : ModalOperator ℓ-zero (λ A → ¬ ¬ A)
  _>>=_ ¬¬modal ¬¬A f ¬B = ¬¬A (λ a → f a ¬B)
  return ¬¬modal a ¬a = ¬a a
