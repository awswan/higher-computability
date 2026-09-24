open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary.Base
open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.Extensions
open import HigherComputability.Dominance.DoubleNegation

open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ using (⊥* ; uninhabEquiv)
open import Cubical.Data.Fin
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)

open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; isPropPropTrunc)

open import HigherComputability.Axioms.MarkovInduction
open import HigherComputability.NeutralRecursive.MarkovsPrinciple

open import HigherComputability.Types.NatInf

open import HigherComputability.Notation.CoercesToType
open import HigherComputability.Notation.Variables

open import HigherComputability.Types.NatInf

open import HigherComputability.Util.DoubleNegation
open import HigherComputability.CubicalExtras.Data.Nat.Properties

module HigherComputability.Dominance.NatInf where

open PreDominance

ℕ∞Pred : PreDominance ℓ-zero ℓ-zero
inDom ℕ∞Pred P = Σ[ α ∈ ℕ∞ ] P ≃ ⟨ α ⟩
onlyProps ℕ∞Pred P (α , e) =
  isOfHLevelRespectEquiv 1 (invEquiv e) (ℕ∞.unique α)
containsUnit ℕ∞Pred = ℕ→ℕ∞ 0 , invEquiv (isContr→≃Unit*
  (inhProp→isContr (ℕ→ℕ∞Ptd 0) (ℕ∞.unique (ℕ→ℕ∞ 0))))
Σclosed ℕ∞Pred {P = P} {Q = Q} (α , e) d =
  ℕ∞Σ α (λ x → fst (d (invEq e x))) ,
  (Σ P Q
    ≃⟨ Σ-cong-equiv-snd (λ p → snd (d p)) ⟩
  Σ[ p ∈ P ] ⟨ fst (d p) ⟩
    ≃⟨ invEquiv (Σ-cong-equiv-fst (invEquiv e)) ⟩
  Σ[ x ∈ ⟨ α ⟩ ] ⟨ fst (d (invEq e x)) ⟩
    ≃⟨ invEquiv (ℕ∞Σ≃ α (λ x → fst (d (invEq e x)))) ⟩
  ⟨ ℕ∞Σ α (λ x → fst (d (invEq e x))) ⟩ ■)

-- the element of ℕ∞ that never hits
ℕ∞Never : ℕ∞
ℕ∞.f ℕ∞Never _ = false
ℕ∞.unique ℕ∞Never (_ , ())

instance
  ℕ∞PredContainsEmpty : ContainsEmpty ℕ∞Pred
  ContainsEmpty.containsEmpty ℕ∞PredContainsEmpty =
    ℕ∞Never , uninhabEquiv ⊥.rec* λ ()

∂ℕ∞ : Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
∂ℕ∞ = ∂ ℕ∞Pred

∂ℕ∞→∂¬¬ : ⦃ _ : MarkovInduction ℓ-zero ⦄ {A : Type ℓa} → ∂ℕ∞ A → ∂¬¬ ℓ A
∂._↓ (∂ℕ∞→∂¬¬ α) = Lift (α ↓)
∂.domainInD (∂ℕ∞→∂¬¬ {ℓ = ℓ} ⦃ mi ⦄ α) = isOfHLevelLift 1 (isPropDomain α) ,
  λ x → lift (equivPreservesStable (invEquiv (snd (domainInD α)))
                              (Stable⟨ℕ∞⟩ (fst (domainInD α)))
                              (¬¬map lower x))
∂.value (∂ℕ∞→∂¬¬ α) x = value α (lower x)

-- Given a decidable family of propositions over ℕ, the type of least
-- witnesses is a proposition of the ℕ∞ dominance: at most one stage of the
-- search succeeds, so the sequence of decisions is itself an element of ℕ∞.
module _ (P : ℕ → Type) (isPropP : (m : ℕ) → isProp (P m))
         (decP : (m : ℕ) → Dec (P m)) where

  private
    dec : (m : ℕ) → Dec (leastSuch P m)
    dec = leastDec decP

    hit : ℕ → Bool
    hit m = Dec→Bool (dec m)

    leastEquiv : (Σ[ m ∈ ℕ ] leastSuch P m) ≃ ⟨ hit ⟩
    leastEquiv =
      Σ-cong-equiv-snd λ m → Dec≃DecBool (isPropLeastSuch isPropP m) (dec m)

  ℕ∞Least : ℕ∞
  ℕ∞.f ℕ∞Least = hit
  ℕ∞.unique ℕ∞Least =
    isOfHLevelRespectEquiv 1 leastEquiv (isPropLeastWitnesses isPropP)

  inDomLeast : PreDominance.inDom ℕ∞Pred (Σ[ m ∈ ℕ ] leastSuch P m)
  inDomLeast = ℕ∞Least , leastEquiv


-- The union of two ℕ∞ propositions: search for the first stage at which
-- either converges. Picking a side records which one got there first (with
-- ties going to the left).
private
  module Union {A B : Type} (inA : PreDominance.inDom ℕ∞Pred A)
               (inB : PreDominance.inDom ℕ∞Pred B) where
    a b : ℕ∞
    a = fst inA
    b = fst inB

    hit : ℕ → Type
    hit k = Bool→Type (ℕ∞.f a k or ℕ∞.f b k)

    L : Type
    L = Σ[ k ∈ ℕ ] leastSuch hit k

    inL : PreDominance.inDom ℕ∞Pred L
    inL = inDomLeast hit (λ _ → isPropBool→Type) (λ _ → DecBool→Type)

    toL : A ⊎ B → L
    toL (inl x) = let (k , p) = equivFun (snd inA) x in
      leastExists (λ _ → DecBool→Type) k (Bool→Type⊎' _ _ (inl p))
    toL (inr y) = let (k , q) = equivFun (snd inB) y in
      leastExists (λ _ → DecBool→Type) k (Bool→Type⊎' (ℕ∞.f a k) _ (inr q))

    fromL : L → A ⊎ B
    fromL (k , h , _) =
      ⊎.map (λ p → invEq (snd inA) (k , p)) (λ q → invEq (snd inB) (k , q))
            (Bool→Type⊎ (ℕ∞.f a k) (ℕ∞.f b k) h)

    fromUnion : ∥ A ⊎ B ∥₁ → L
    fromUnion = PT.rec (onlyProps ℕ∞Pred L inL) toL

instance
  ℕ∞PredSupportsUnionAndPick : SupportsUnionAndPick ℕ∞Pred
  SupportsUnionAndPick.unionInDom ℕ∞PredSupportsUnionAndPick inA inB =
    fst inL ,
    propBiimpl→Equiv isPropPropTrunc (onlyProps ℕ∞Pred L inL) fromUnion
      (λ l → ∣ fromL l ∣₁)
    ∙ₑ snd inL
    where open Union inA inB
  SupportsUnionAndPick.pick ℕ∞PredSupportsUnionAndPick inA inB w =
    fromL (fromUnion w)
    where open Union inA inB
