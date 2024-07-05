open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary.Base

open import Cubical.Functions.Embedding

open import Cubical.Data.Bool
open import CubicalExtras.Data.Bool.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Dominance.Base

open import Notation.Variables

module Dominance.Bool where

open PreDominance


BoolPred : PreDominance ℓ ℓ
inDom BoolPred P = Σ[ b ∈ Bool ] Bool→Type b ≃ P
onlyProps BoolPred P (b , e) = isOfHLevelRespectEquiv 1 e isPropBool→Type
containsUnit BoolPred = true , Unit≃Unit*
Σclosed BoolPred (b , e) Qdata =
  ΣBool b (λ x → fst (Qdata (equivFun e x))) ,
  ΣBool≃Σ ∙ₑ Σ-cong-equiv e λ x → snd (Qdata (equivFun e x))

∂Bool : Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ'))
∂Bool {ℓ' = ℓ'} = ∂ (BoolPred {ℓ = ℓ'})

isDefinedAndDec : {A : Type ℓa} {P : A → Type ℓ} →
  ((a : A) → Dec (P a)) → (α : ∂Bool {ℓ' = ℓ} A) → Dec (α ↓= a & P a)
isDefinedAndDec {ℓ = ℓ} {P = P} dec α = helper (domainInD α)
  where
    helper : (x : inDom BoolPred (α ↓)) → Dec (α ↓= a & P a)
    helper (false , e) = no (λ (α↓ , _) → invEq e α↓)
    helper (true , e) =
      decRec (λ p → yes (α↓ , p))
             (λ ¬p → no (λ (α↓' , p) → ¬p (subst (P ∘ value α) (isPropDomain α α↓' α↓) p)))
             (dec (value α α↓))
      where
        α↓ : α ↓
        α↓ = equivFun e tt
