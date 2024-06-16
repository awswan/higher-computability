open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Notation.ModalOperatorSugar

open import Notation.Variables

module Notation.ModalOpInstances.PropositionalTruncation where

instance
  modalOpPropTrunc : ModalOperator ℓ-zero ℓ ℓ' ∥_∥₁
  ModalOperator.bind modalOpPropTrunc α f = rec isPropPropTrunc f α
