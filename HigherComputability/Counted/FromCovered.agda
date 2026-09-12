open import Cubical.Foundations.Prelude
open import Cubical.Functions.Surjection
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
open import HigherComputability.Dominance.Base
open import HigherComputability.Counted.Base

open import HigherComputability.Notation.ModalOperatorSugar
open import HigherComputability.Notation.Variables

module HigherComputability.Counted.FromCovered where

countedFromCovered : {B : Type ℓ'} (A : Type ℓ) ⦃ ctdA : Counted A ⦄ →
  A ↠ B → Counted B
Counted.enum (countedFromCovered {B = B} A ⦃ ctdA ⦄ s) n =
  enum ⦃ ctdA ⦄ n >>= λ a → return (fst s a)
Counted.isSurjEnum (countedFromCovered {B = B} A ⦃ ctdA ⦄ s) b =
  rec isPropPropTrunc
      (λ (a , fa≡b) →
        map (λ (n , (enumn↓ , enumn≡a)) →
               n , ((enumn↓ , tt*) , (cong (fst s) enumn≡a ∙ fa≡b)))
            (isSurjEnum ⦃ ctdA ⦄ a))
      (snd s b)
