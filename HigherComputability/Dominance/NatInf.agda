open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary.Base
open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.DoubleNegation

open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Fin
open import Cubical.Data.Bool
open import Cubical.Data.Sum using (_⊎_; inl; inr)

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


private
  pick : (x y : Bool) → Bool→Type (x or y) → Bool→Type x ⊎ Bool→Type y
  pick true _ p = inl p
  pick false _ p = inr p

  orL : (x y : Bool) → Bool→Type x → Bool→Type (x or y)
  orL true _ p = p

  orR : (x y : Bool) → Bool→Type y → Bool→Type (x or y)
  orR true _ _ = tt
  orR false _ p = p

-- Run two partial elements in parallel, stopping at the first stage at which
-- either converges. The value records which one got there first (with ties
-- going to the left).
module _ {A : Type ℓa} {B : Type ℓb} (α : ∂ℕ∞ A) (β : ∂ℕ∞ B) where
  private
    a b : ℕ∞
    a = fst (domainInD α)
    b = fst (domainInD β)

    hit : ℕ → Type
    hit k = Bool→Type (ℕ∞.f a k or ℕ∞.f b k)

  race : ∂ℕ∞ ((α ↓) ⊎ (β ↓))
  race ↓ = Σ[ k ∈ ℕ ] leastSuch hit k
  domainInD race = inDomLeast hit (λ _ → isPropBool→Type) (λ _ → DecBool→Type)
  value race (k , h , _) with pick (ℕ∞.f a k) (ℕ∞.f b k) h
  ... | inl p = inl (invEq (snd (domainInD α)) (k , p))
  ... | inr q = inr (invEq (snd (domainInD β)) (k , q))

  raceDefL : α ↓ → race ↓
  raceDefL z = leastExists (λ _ → DecBool→Type) k (orL _ _ p)
    where
      k = fst (equivFun (snd (domainInD α)) z)
      p = snd (equivFun (snd (domainInD α)) z)

  raceDefR : β ↓ → race ↓
  raceDefR z = leastExists (λ _ → DecBool→Type) k (orR (ℕ∞.f a k) _ q)
    where
      k = fst (equivFun (snd (domainInD β)) z)
      q = snd (equivFun (snd (domainInD β)) z)
