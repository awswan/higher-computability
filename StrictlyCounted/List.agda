open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import StrictlyCounted.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.List.Base
open import Cubical.Data.List.Properties
open import Cubical.Data.List.FinData
open import Cubical.Data.FinData
open import Cubical.Data.Sum
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty

open import Encodings.SumUnit

open import StrictlyCounted.Sigma
open import StrictlyCounted.Nat

open import Notation.Variables

module StrictlyCounted.List where

abstract instance
  vecSCtd : {A : Type ℓa} ⦃ _ : StrictlyCounted A ⦄ → {n : ℕ} →
    StrictlyCounted (Fin (suc n) → A)
  StrictlyCounted.sCtdEquiv (vecSCtd {n = zero}) =
    sCtdEquiv ∙ₑ invEquiv (isoToEquiv (isContr→Iso2 isContrFin1))
  StrictlyCounted.sCtdEquiv (vecSCtd {A = A} {n = suc n}) =
    ℕ ≃⟨ sCtdEquiv ⟩
    A × ℕ ≃⟨ ≃-× (invEquiv (ΠUnit _)) (StrictlyCounted.sCtdEquiv vecSCtd) ⟩
    (Unit → A) × (Fin (suc n) → A) ≃⟨ invEquiv Π⊎≃ ⟩
    (Unit ⊎ Fin (suc n) → A) ≃⟨ preCompEquiv (pathToEquiv Maybe≡SumUnit) ⟩
    (Maybe (Fin (suc n)) → A) ≃⟨ preCompEquiv (isoToEquiv finSucMaybeIso) ⟩
    (Fin (suc (suc n)) → A) ■

  sCtdList : {A : Type ℓa} ⦃ _ : StrictlyCounted A ⦄ →
    StrictlyCounted (List A)
  StrictlyCounted.sCtdEquiv (sCtdList {ℓa = ℓa} {A = A}) =
    ℕ ≃⟨ ℕSumUnitEquiv ⟩
    ℕ ⊎ Unit
      ≃⟨ ⊎-equiv (idEquiv _) (invEquiv (isContr→≃Unit isContr⊥→A)) ⟩
    ℕ ⊎ (⊥ → A)
      ≃⟨ ⊎-equiv sCtdEquiv
                 (invEquiv ((ΣUnit _) ∙ₑ preCompEquiv (uninhabEquiv (λ x → x) ¬Fin0))) ⟩
    (Σ[ n ∈ ℕ ] (Fin (suc n) → A)) ⊎ (Σ[ x ∈ Unit ] (Fin 0 → A))
      ≃⟨ invEquiv Σ⊎≃ ⟩
    Σ[ x ∈ ℕ ⊎ Unit ] (Fin (invEq ℕSumUnitEquiv x) → A)
      ≃⟨ Σ-cong-equiv-fst (invEquiv ℕSumUnitEquiv) ⟩
    Σ[ n ∈ ℕ ] (Fin n → A)
      ≃⟨ invEquiv (lookup-tabulate-equiv A) ⟩
    List A ■
