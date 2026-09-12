open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Nat

open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.DoubleNegation

open import HigherComputability.Axioms.ComputableChoice
open import HigherComputability.Axioms.MarkovInduction

open import HigherComputability.Notation.Variables

module HigherComputability.FirstKleene.Base where

module _ ⦃ _ : ComputableChoice ⦄ {ℓ : Level}  where
  open import HigherComputability.Axioms.Generalities {ℓ = ℓ} separatedℕ φ computableChoice

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
