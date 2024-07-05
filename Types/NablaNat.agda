open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (elim)

open import Types.PropNegNeg
open import Types.NablaZero

open import Notation.CoercesToType

module Types.NablaNat {ℓ : Level} where

isSuc : ℕ → ℕ → hProp¬¬ ℓ
hProp¬¬.P (isSuc n m) = Lift (suc n ≡ m)
hProp¬¬.isPropP (isSuc n m) = isOfHLevelLift 1 (isSetℕ (suc n) m)
hProp¬¬.StableP (isSuc n m) ¬¬p = lift (separatedℕ (suc n) m (¬¬map lower ¬¬p))

isSuc∇₀ : ∇₀ {ℓ = ℓ} ℕ → ∇₀ {ℓ = ℓ} ℕ → hProp¬¬ ℓ
isSuc∇₀ = ExtendBinaryRelation.R̃ ℕ isSuc

nonZeroToPredecessor : (ν : ∇₀ ℕ) → ¬ ⟨ ∇₀.isThis ν 0 ⟩ →
  Σ[ μ ∈ (∇₀ ℕ) ] ⟨ isSuc∇₀ μ ν ⟩

nonZeroToPredecessor ν n≢0 = μ ,
  λ n m u v → lift (separatedℕ (suc n) m (∇₀.wellDefd ν (suc n) m u v))
  where
    μ : ∇₀ ℕ
    ∇₀.isThis μ m = ∇₀.isThis ν (suc m)
    ∇₀.wellDefd μ m m' u u' = ¬¬map injSuc (∇₀.wellDefd ν (suc m) (suc m') u u')
    ∇₀.almostInh μ = ¬¬map (λ (n , u) → (predℕ n) ,
      (subst (λ n → ⟨ ∇₀.isThis ν n ⟩))
      (suc-predℕ n (λ p → n≢0 (subst (λ n → ⟨ ∇₀.isThis ν n ⟩) p u))) u) (∇₀.almostInh ν)

definedToSuc : (μ ν : ∇₀ ℕ) (is : ⟨ isSuc∇₀ μ ν ⟩) (m : ℕ) → ⟨ ∇₀.isThis μ m ⟩ →
  ⟨ ∇₀.isThis ν (suc m) ⟩
definedToSuc μ ν is m p = hProp¬¬.StableP (∇₀.isThis ν (suc m))
  (¬¬map (λ (n , x) → subst (λ n' → ⟨ ∇₀.isThis ν n' ⟩)
                            (sym (lower (is m n p x))) x) (∇₀.almostInh ν))

definedToPred : (μ ν : ∇₀ ℕ) (is : ⟨ isSuc∇₀ μ ν ⟩) (m : ℕ) → ⟨ ∇₀.isThis ν (suc m) ⟩ →
  ⟨ ∇₀.isThis μ m ⟩
definedToPred μ ν is m p = hProp¬¬.StableP (∇₀.isThis μ m)
  (¬¬map (λ (m' , x) → subst (λ m' → ⟨ ∇₀.isThis μ m' ⟩)
                            (injSuc (lower (is m' (suc m) x p))) x) (∇₀.almostInh μ))
