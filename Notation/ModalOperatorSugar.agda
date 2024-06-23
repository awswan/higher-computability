open import Cubical.Foundations.Prelude

module Notation.ModalOperatorSugar where

record ModalOperator (ℓbase : Level) (M : {ℓ' : Level} → Type ℓ' →
  Type (ℓ-max ℓbase ℓ')) : Typeω where
  field
    _>>=_ : {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} → M A → (A → M B) → M B
    return : {ℓb : Level} {B : Type ℓb} → B → M B

open ModalOperator ⦃...⦄ public

-- _>>=_ : {ℓbase ℓa ℓb : Level} {M : {ℓ' : Level} → Type ℓ' → Type (ℓ-max ℓbase ℓ')} → 
--         ⦃ mo : ModalOperator ℓbase ℓa ℓb M ⦄ →
--         {A : Type ℓa} {B : Type ℓb} →
--         M A → (A → M B) → M B
-- _>>=_ ⦃ mo ⦄ = ModalOperator.bind mo
