open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr) renaming (rec to rec⊎)

open import Cubical.Relation.Nullary.Base

open import Cubical.HITs.PropositionalTruncation

open import HigherComputability.Dominance.Base
open import HigherComputability.Dominance.DoubleNegation
open import HigherComputability.Dominance.NatInf

open import HigherComputability.Axioms.ComputableChoice
open import HigherComputability.Axioms.MarkovInduction

open import HigherComputability.FirstKleene.Base

module HigherComputability.FirstKleene.PreciseExtendedChurchsThesis where

private
  ¬n≡sucn : (n : ℕ) → ¬ n ≡ suc n
  ¬n≡sucn zero p = znots p
  ¬n≡sucn (suc n) p = ¬n≡sucn n (injSuc p)

module _ ⦃ _ : ComputableChoice ⦄ ⦃ _ : MarkovInduction ℓ-zero ⦄ where
  private
    -- Race f n against φ e n. If f n converges first we return its value,
    -- but if φ e n converges first we return something different from it.
    raceφ : (ℕ → ∂ℕ∞ ℕ) → ℕ → ℕ → ∂ℕ∞ ℕ
    raceφ f e n ↓ = race (f n) (φ e n) ↓
    domainInD (raceφ f e n) = domainInD (race (f n) (φ e n))
    value (raceφ f e n) d =
      rec⊎ (value (f n)) (λ z → suc (value (φ e n) z)) (value (race (f n) (φ e n)) d)

    -- If φ e n agrees with the race, then f must have won it.
    fWon : (f : ℕ → ∂ℕ∞ ℕ) (e n : ℕ) (w : (f n ↓) ⊎ (φ e n ↓)) (z : φ e n ↓) →
      value (φ e n) z ≡ rec⊎ (value (f n)) (λ z → suc (value (φ e n) z)) w →
      f n ↓= a & a ≡ value (φ e n) z
    fWon f e n (inl y) z p = y , sym p
    fWon f e n (inr y) z p =
      rec⊥ (¬n≡sucn _ (p ∙ cong (suc ∘ value (φ e n)) (isPropDomain (φ e n) y z)))

  -- Every partial function on ℕ with ℕ∞ domains is computable, with the index
  -- having exactly the same domain, not just an extension of it.
  preciseECT : (f : ℕ → ∂ℕ∞ ℕ) → ∥ Σ[ e ∈ ℕ ] (f ⊑ φ e) × (φ e ⊑ f) ∥₁
  preciseECT f =
    map (λ (e , fix) → e , left e fix , right e fix)
        (recursionThm {ℓ = ℓ-zero} (λ e n → ∂ℕ∞→∂¬¬ (raceφ f e n)))
    where
      left : (e : ℕ) → (λ n → ∂ℕ∞→∂¬¬ {ℓ = ℓ-zero} (raceφ f e n)) ⊑ φ e → f ⊑ φ e
      left e fix n y =
        z , sym q ∙ cong (value (f n)) (isPropDomain (f n) y' y)
        where
          d = raceDefL (f n) (φ e n) y
          z = fst (fix n (lift d))
          p = snd (fix n (lift d))
          y' = fst (fWon f e n (value (race (f n) (φ e n)) d) z p)
          q = snd (fWon f e n (value (race (f n) (φ e n)) d) z p)

      right : (e : ℕ) → (λ n → ∂ℕ∞→∂¬¬ {ℓ = ℓ-zero} (raceφ f e n)) ⊑ φ e → φ e ⊑ f
      right e fix n z =
        y , q ∙ cong (value (φ e n)) (isPropDomain (φ e n) z' z)
        where
          d = raceDefR (f n) (φ e n) z
          z' = fst (fix n (lift d))
          p = snd (fix n (lift d))
          y = fst (fWon f e n (value (race (f n) (φ e n)) d) z' p)
          q = snd (fWon f e n (value (race (f n) (φ e n)) d) z' p)
