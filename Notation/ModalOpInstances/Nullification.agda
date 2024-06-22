open import Cubical.Foundations.Prelude
open import Notation.ModalOperatorSugar
open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.Nullification.Properties

open import Notation.Variables

module Notation.ModalOpInstances.Nullification where

open ModalOperator

instance
  bindNull : {ℓa ℓs : Level} {A : Type ℓa} {S : A → Type ℓs} →
    ModalOperator (ℓ-max ℓa ℓs) ℓ ℓ' (Null S)
  bind bindNull α f = rec (isNull-Null _) f α
