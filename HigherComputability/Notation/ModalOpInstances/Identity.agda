open import Cubical.Foundations.Prelude
open import HigherComputability.Notation.ModalOperatorSugar

module HigherComputability.Notation.ModalOpInstances.Identity where

open ModalOperator

instance
  idModal : ModalOperator ℓ-zero (λ A → A)
  _>>=_ idModal a f = f a
  return idModal a = a
