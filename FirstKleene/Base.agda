open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Nat

open import Dominance.Base
open import Dominance.DoubleNegation

open import Axioms.ComputableChoice
open import Axioms.MarkovInduction

open import Notation.Variables

module FirstKleene.Base where

module _ ⦃ _ : ComputableChoice ⦄ {ℓ : Level}  where
  open import Axioms.Generalities {ℓ = ℓ} separatedℕ φ computableChoice

  totalComputableChoice = totalVersion
  ECT = functionalVersion

  module _ ⦃ _ : MarkovInduction ℓ-zero ⦄ where
    snm = WithMP.twoArgFunVersion -- TODO: check if this is really the snm theorem
    recursionThm = WithMP.fixedPoint

record EffectiveAxioms : Typeω where
  field
    mi : {ℓ : Level} → MarkovInduction ℓ
    ct : ComputableChoice

open EffectiveAxioms ⦃...⦄ public
