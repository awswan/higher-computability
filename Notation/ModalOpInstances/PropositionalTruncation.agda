open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Notation.ModalOperatorSugar

open import Notation.Variables

module Notation.ModalOpInstances.PropositionalTruncation where

open ModalOperator

instance
  modalOpPropTrunc : ModalOperator ℓ-zero ∥_∥₁
  _>>=_ modalOpPropTrunc α f = rec isPropPropTrunc f α
  return modalOpPropTrunc = ∣_∣₁
