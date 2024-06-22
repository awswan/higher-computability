open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base

open import Cubical.HITs.PropositionalTruncation

open import StrictlyCounted.Base
open import Subcounted.Base

open import Dominance.Base
open import Dominance.DoubleNegation

-- open import Partiality.Base

open import Types.PropNegNeg

open import Notation.CoercesToType
open import Notation.Variables

module FirstKleene.SubcountableChoice
  {ℓA ℓsca : Level} {A : Type ℓA} ⦃ sctdA : Subcounted ℓsca A ⦄
  {ℓB ℓscb : Level} {B : Type ℓB} ⦃ sctdB : Subcounted ℓscb B ⦄
  where

-- module SCA = Subcounted sctdA

-- enumSCtdToSubctd : ℕ → A → ∂ℕ∞ B

-- generalisedCC : {ℓd ℓp : Level} 
--   (D : A → hProp¬¬ ℓd) →
--   (P : (a : A) → (d : ⟨ D a ⟩) → B → hProp¬¬ ℓp) →
--   (total : (a : A) → (d : ⟨ D a ⟩) → ∥ Σ[ b ∈ B ] ⟨ P a d b ⟩ ∥₁) →
--   ∥ (Σ[ e ∈ ℕ ] ((n : ℕ) → (d : ⟨ D {!!} ⟩) → {!!} )) ∥₁

-- subcountableChoice : {ℓd ℓp : Level} 
--   (D : A → hProp¬¬ ℓd) →
--   (P : (a : A) → (d : ⟨ D a ⟩) → B → hProp¬¬ ℓp) →
--   (total : (a : A) → (d : ⟨ D a ⟩) → ∥ Σ[ b ∈ B ] ⟨ P a d b ⟩ ∥₁) →
--   ∥ Σ[ f ∈ (A → ∂¬¬ ℓ'' B) ] ((a : A) → (d : ⟨ D a ⟩) → f a ↓= b & ⟨ P a d b ⟩) ∥₁
  
-- subcountableChoice D P total = {!!}
