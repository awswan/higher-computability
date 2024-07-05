open import Cubical.Foundations.Prelude
open import Notation.ModalOperatorSugar

module Notation.ModalOpInstances.Identity where

open ModalOperator

instance
  idModal : ModalOperator ℓ-zero (λ A → A)
  _>>=_ idModal a f = f a
  return idModal a = a
