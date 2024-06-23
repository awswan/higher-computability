open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sum.Base
open import Cubical.Data.Sigma.Properties
open import NeutralRecursive.RelativisedMP

open import Notation.ModalOperatorSugar
open import Notation.Variables

module NeutralRecursive.ParallelSearch
  {ℓbase : Level}
  (M : {ℓ : Level} → Type ℓ → Type (ℓ-max ℓbase ℓ))
  ⦃ _ : ModalOperator ℓbase M ⦄
  where

parallelSearch : (P Q : ℕ → Type ℓ) (decP : (n : ℕ) → M (Dec (P n)))
  (decQ : (n : ℕ) → M (Dec (Q n))) →
  NonEmpty (Σ ℕ P ⊎ Σ ℕ Q) → M (Σ ℕ P ⊎ Σ ℕ Q)
parallelSearch {ℓ} P Q decP decQ ¬¬exists = do
  (n , p⊎q) ← search M PQ decPQ ¬¬existsPQ
  return (rec (λ p → inl (n , p)) (λ q → inr (n , q)) p⊎q)
  where
    PQ : ℕ → Type ℓ
    PQ n = P n ⊎ Q n

    decPQ : (n : ℕ) → M (Dec (PQ n))
    decPQ n = do
      no ¬p ← decP n
        where yes p → return (yes (inl p))
      no ¬q ← decQ n
        where yes q → return (yes (inr q))
      return (no (rec ¬p ¬q))

    ¬¬existsPQ : NonEmpty (Σ ℕ PQ)
    ¬¬existsPQ = ¬¬map (rec (map-snd inl) (map-snd inr)) ¬¬exists
