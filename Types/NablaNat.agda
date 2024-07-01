open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.HITs.Nullification
open import Cubical.Data.Nat hiding (elim)

open import Types.DoubleNegationSheaves

module Types.NablaNat {ℓ : Level} where

isSucc : ℕ → ℕ → NullType (DenseProps ℓ) {ℓ = ℓ}
isSucc n m = Lift (suc n ≡ m) , StableProp→Sheaf (λ x → lift (separatedℕ (suc n) m (¬¬map lower x))) (isOfHLevelRespectEquiv 1 LiftEquiv (isSetℕ _ _)) -- StableProp→Sheaf _ (separatedℕ _ _) (isSetℕ _ _)

isSucc₀ : ℕ → ℕ → NullType (DenseProps ℓ-zero) {ℓ = ℓ-zero}
isSucc₀ n m = (suc n ≡ m) , (StableProp→Sheaf (λ x → separatedℕ (suc n) m x)
                            (isSetℕ (suc n) m))

isSucc∇ : ∇ ℕ → ∇ ℕ → NullType (DenseProps ℓ) {ℓ = ℓ}
isSucc∇ =
  rec (isNullΠ λ _ → isNullNullTypes (DenseProps ℓ) (snd ∘ fst) {ℓ = ℓ})
      λ n → rec (isNullNullTypes (DenseProps ℓ) (snd ∘ fst) {ℓ = ℓ})
      λ m → isSucc n m -- isSucc n m

isSucc∇₀ : ∇ {ℓ = ℓ-zero} ℕ → ∇ {ℓ = ℓ-zero}
  ℕ → NullType (DenseProps ℓ-zero) {ℓ = ℓ-zero}
isSucc∇₀ =
  rec (isNullΠ (λ _ → isNullNullTypes (DenseProps ℓ-zero) λ ((_ , propP) , _) → propP))
      λ n → rec (isNullNullTypes (DenseProps ℓ-zero) (λ ((_ , propP) , _) → propP))
      (λ m → isSucc₀ n m)

nonZeroToPredecessor : (ν : ∇ ℕ) → ¬ (ν ≡ ∣ 0 ∣) →
  Σ[ μ ∈ ∇ ℕ ] fst (isSucc∇ μ ν)
nonZeroToPredecessor = elim (λ ν → isNullΠ (λ _ → isNullΣ (isNull-Null _) λ μ → snd (isSucc∇ μ ν)))
  (λ n n≠0 → ∣ predℕ n ∣ , lift (sym (suc-predℕ n λ p → n≠0 (cong ∣_∣ p))))

definedToSuc : {μ ν : ∇ ℕ} (is : fst (isSucc∇ μ ν)) (m : ℕ) → (μ ≡ ∣ m ∣) →
  (ν ≡ ∣ suc m ∣)
definedToSuc {μ} {ν} is m p = lemma ν (subst (λ z → fst (isSucc∇ z ν)) p is)
  where
    lemma : (ν : ∇ ℕ) → (fst (isSucc∇ ∣ m ∣ ν )) → (ν ≡ ∣ suc m ∣)
    lemma = elim (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null _))) λ n p → cong ∣_∣ (sym (lower p))

definedToPred : {μ ν : ∇ ℕ} (is : fst (isSucc∇ μ ν)) (m : ℕ) → (ν ≡ ∣ suc m ∣) →
  (μ ≡ ∣ m ∣)
definedToPred {μ} {ν} is m p = lemma μ (subst (λ z → fst (isSucc∇ μ z)) p is)
  where
    lemma : (μ : ∇ ℕ) → (fst (isSucc∇ μ ∣ suc m ∣)) → μ ≡ ∣ m ∣
    lemma = elim (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null _)))
      λ n p → cong ∣_∣ (injSuc (lower p))
