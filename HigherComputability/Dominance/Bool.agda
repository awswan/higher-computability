open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.Extensions
open import HigherComputability.Dominance.DoubleNegation

open import HigherComputability.Notation.Variables

open import HigherComputability.Util.DoubleNegation

module HigherComputability.Dominance.Bool where

open PreDominance


BoolPred : PreDominance ℓ ℓ
inDom BoolPred P = Σ[ b ∈ Bool ] Bool→Type b ≃ P
onlyProps BoolPred P (b , e) = isOfHLevelRespectEquiv 1 e isPropBool→Type
containsUnit BoolPred = true , Unit≃Unit*
Σclosed BoolPred (b , e) Qdata =
  ΣBool b (λ x → fst (Qdata (equivFun e x))) ,
  ΣBool≃Σ ∙ₑ Σ-cong-equiv e λ x → snd (Qdata (equivFun e x))

instance
  BoolPredContainsEmpty : ContainsEmpty (BoolPred {ℓ = ℓ})
  ContainsEmpty.containsEmpty BoolPredContainsEmpty = false , LiftEquiv

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

-- Every proposition in the Bool dominance is decidable, hence stable, so the
-- Bool dominance is contained in the double negation dominance.
∂BoolDomainStable : {A : Type ℓa} (α : ∂Bool {ℓ' = ℓ} A) → Stable (α ↓)
∂BoolDomainStable α =
  equivPreservesStable (snd (domainInD α)) (Dec→Stable DecBool→Type)

∂Bool→∂¬¬ : {A : Type ℓa} → ∂Bool {ℓ' = ℓ} A → ∂¬¬ (ℓ-max ℓ ℓ') A
_↓ (∂Bool→∂¬¬ {ℓ' = ℓ'} α) = Lift {j = ℓ'} (α ↓)
domainInD (∂Bool→∂¬¬ α) = isOfHLevelLift 1 (isPropDomain α) ,
  (λ ¬¬d → lift (∂BoolDomainStable α (¬¬map lower ¬¬d)))
value (∂Bool→∂¬¬ α) d = value α (lower d)
