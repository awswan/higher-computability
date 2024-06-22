open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded

open import Types.NablaNat

open import Misc

open import Notation.ModalOperatorSugar

open import Types.DoubleNegationSheaves

module Axioms.MarkovInduction {ℓ : Level} where

postulate
  wellFounded∇Suc : WellFounded {ℓ' = ℓ} (λ μ ν → fst (isSucc∇ μ ν))
  
markovInduction = WFI.induction wellFounded∇Suc
