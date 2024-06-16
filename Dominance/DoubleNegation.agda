open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Types.PropNegNeg

open import Dominance.Base

open import Notation.Variables
open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.DoubleNegation

open import Misc

module Dominance.DoubleNegation where

¬¬PreDom : (ℓ : Level) → PreDominance {ℓ = ℓ-suc ℓ} {ℓ' = ℓ}
PreDominance.Idx (¬¬PreDom ℓ) = hProp¬¬ ℓ
PreDominance.P (¬¬PreDom ℓ) = hProp¬¬.P
PreDominance.isPropP (¬¬PreDom ℓ) = hProp¬¬.isPropP

¬¬Dom : (ℓ ℓ' : Level) → Dominance {ℓ = ℓ-suc ℓ} {ℓ' = ℓ}
Dominance.pred (¬¬Dom ℓ ℓ') = ¬¬PreDom ℓ
Dominance.isEmbeddingP (¬¬Dom ℓ ℓ') = hProp¬¬isEmbedP
hProp¬¬.P (Dominance.ΣLift (¬¬Dom ℓ ℓ') p q) = Σ (hProp¬¬.P p) (hProp¬¬.P ∘ q)
hProp¬¬.isPropP (Dominance.ΣLift (¬¬Dom ℓ ℓ') p q) =
  isPropΣ (hProp¬¬.isPropP p) λ x → hProp¬¬.isPropP (q x)
hProp¬¬.StableP (Dominance.ΣLift (¬¬Dom ℓ ℓ') p q) =
  StableΣ (hProp¬¬.StableP p) (hProp¬¬.isPropP p) (hProp¬¬.StableP ∘ q)
Dominance.ΣLiftIsΣ (¬¬Dom ℓ ℓ') = refl

∂¬¬ : (ℓ' : Level) → Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ'))
∂¬¬ ℓ' = ∂Pred (¬¬PreDom ℓ')
