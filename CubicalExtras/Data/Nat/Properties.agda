open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Fin.Base hiding (elim)
open import Cubical.Induction.WellFounded

open import Notation.Variables

module CubicalExtras.Data.Nat.Properties where

leastSuch : (P : ℕ → Type ℓ) → ℕ → Type ℓ
leastSuch P n = P n × ((m : ℕ) → m < n → ¬ P m)

module _ {P : ℕ → Type ℓ} where
  isPropLeastSuch : ((n : ℕ) → isProp (P n)) → (n : ℕ) →
    isProp (leastSuch P n)
  isPropLeastSuch propP n = isProp× (propP n) (isPropΠ3 λ _ _ _ → isProp⊥)

  StableLeastSuch : ((n : ℕ) → Stable (P n)) → (n : ℕ) → Stable (leastSuch P n)
  StableLeastSuch stableP n = Stable× (stableP n) (StableΠ (λ _ → Stable→ Stable¬))

  leastUnique : (n m : ℕ) → (leastSuch P n) → (leastSuch P m) → n ≡ m
  leastUnique n m x y with n ≟ m
  ... | lt p = ⊥rec (snd y n p (fst x))
  ... | gt p = ⊥rec (snd x m p (fst y))
  ... | eq p = p

  isPropLeastWitnesses : ((n : ℕ) → isProp (P n)) →
    isProp (Σ[ n ∈ ℕ ] (leastSuch P n))
  isPropLeastWitnesses propP (n , p) (m , q) =
    Σ≡Prop (λ n → isPropLeastSuch propP n) (leastUnique n m p q)

  leastExists : (decP : (n : ℕ) → Dec (P n)) →
    (n : ℕ) → P n → Σ[ n ∈ ℕ ] leastSuch P n
  leastExists decP =
    WFI.induction <-wellfounded
      λ n ih p →
        decRec (λ ((m , l) , q) → ih m l q)
               (λ z → n , (p , (λ m l q → z ((m , l) , q))))
               (any? λ (m , _) → decP m )

  leastDec : ((n : ℕ) → Dec (P n)) → (n : ℕ) → Dec (leastSuch P n)
  leastDec dec n with (dec n)
  ... | no ¬p = no (λ (p , l) → ¬p p)
  ... | yes p with any? (λ (m , _) → dec m)
  ... | yes ((m , l) , q) = no (λ (_ , f) → f m l q)
  ... | no ¬q = yes (p , (λ m l q → ¬q ((m , l) , q)))
