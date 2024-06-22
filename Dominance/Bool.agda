open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.Data.Bool
open import CubicalExtras.Data.Bool.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Dominance.Base

open import Misc
open import Notation.Variables

module Dominance.Bool where

open PreDominance

opaque
  BoolPred : PreDominance ℓ ℓ
  inDom BoolPred P = Σ[ b ∈ Bool ] Bool→Type b ≃ P
  onlyProps BoolPred P (b , e) = isOfHLevelRespectEquiv 1 e isPropBool→Type
  containsUnit BoolPred = true , Unit≃Unit*
  Σclosed BoolPred (b , e) Qdata =
    ΣBool b (λ x → fst (Qdata (equivFun e x))) ,
    ΣBool≃Σ ∙ₑ Σ-cong-equiv e λ x → snd (Qdata (equivFun e x))

∂Bool : Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ'))
∂Bool {ℓ' = ℓ'} = ∂ (BoolPred {ℓ = ℓ'})
