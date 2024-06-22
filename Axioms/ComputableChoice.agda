open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties


open import Dominance.Base
open import Dominance.NatInf
-- open import Partiality.Base
open import Types.PropNegNeg
open import Dominance.DoubleNegation

open import Notation.Variables
open import Notation.CoercesToType

--open import Misc

module Axioms.ComputableChoice where

postulate
  φ : ℕ → ℕ → ∂ℕ∞ ℕ

  ComputableChoice : (R : ℕ → ℕ → hProp¬¬ ℓ) →
    ((n : ℕ) → ¬ ¬ (Σ[ m ∈ ℕ ] ⟨ R n m ⟩) → ∥ Σ[ m ∈ ℕ ] ⟨ R n m ⟩ ∥₁) →
    ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → ¬ ¬ (Σ[ m ∈ ℕ ] ⟨ R n m ⟩) →
                     φ e n ↓= m & ⟨ R n m ⟩) ∥₁
  
ComputableChoice' :
  (D : ℕ → Type ℓ) (DProp : (n : ℕ) → isProp (D n))
  (DStab : (n : ℕ) → Stable (D n))
  (P : (n : ℕ) → (d : D n) → ℕ → Type ℓ')
  (PProp : (n : ℕ) → (d : D n) → (m : ℕ) → isProp (P n d m))
  (PStab : (n : ℕ) → (d : D n) → (m : ℕ) →
    Stable (P n d m))
  (Pinh : (n : ℕ) → (d : D n) → ∥ Σ[ m ∈ ℕ ] P n d m ∥₁) →
  ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (d : D n) →
                   φ e n ↓= m & P n d m) ∥₁

ComputableChoice' D DProp DStab P PProp PStab Pinh =
  map (λ (e , f) → e ,
    (λ n d → map-snd (λ (d' , p) → subst (λ d → P n d _) (DProp n _ _) p)
                     (f n (rec (isPropΠ (λ _ → isProp⊥))
                               (λ (m , p) y → y (m , (d , p))) (Pinh n d))) ))
    CCinstance
  where
    R' : ℕ → ℕ → hProp¬¬ _
    hProp¬¬.P (R' n m) = Σ[ d ∈ D n ] P n d m
    hProp¬¬.isPropP (R' n m) = isPropΣ (DProp n) λ d → PProp n d m
    hProp¬¬.StableP (R' n m) = StableΣ (DStab n) (DProp n) (λ d → PStab n d m)

    R'inh : (n : ℕ) → ¬ ¬ (Σ[ m ∈ ℕ ] ⟨ R' n m ⟩) →
      ∥ Σ[ m ∈ ℕ ] ⟨ R' n m ⟩ ∥₁
    R'inh n d = map
      (λ (m , z) → m , d' , z)
      (Pinh n d')
      where
        d' : D n
        d' = DStab n (¬¬map (λ (_ , (d , _)) → d) d)

    CCinstance : ∥ Σ[ e ∈ ℕ ] ((n : ℕ) →  ¬ ¬ (Σ[ m ∈ ℕ ] ⟨ R' n m ⟩) →
      φ e n ↓= m & ⟨ R' n m ⟩) ∥₁
    CCinstance = ComputableChoice R' R'inh

-- ECT : (f : ℕ → ∂¬¬ ℓ ℕ) → ∥ (Σ[ e ∈ ℕ ] ((n : ℕ) → f n ⊑ φ e n)) ∥₁
-- ECT {ℓ = ℓ} f = {!!} -- map (λ (e , z) → e , {!!}) (ComputableChoice R Rdefd)
--   where
