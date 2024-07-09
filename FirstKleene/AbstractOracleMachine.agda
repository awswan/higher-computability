open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma
open import Cubical.Data.List.Base
open import Cubical.Data.Sum.Base

open import StrictlyCounted.Base
open import StrictlyCounted.Properties
open import StrictlyCounted.List
open import StrictlyCounted.Nat
open import StrictlyCounted.Sum
open import StrictlyCounted.Sigma

module FirstKleene.AbstractOracleMachine where

data AbstractOracleMachine : Type where
  returnValue : (n : ℕ) → AbstractOracleMachine
  queryAndContinue : (n : ℕ) → (e : ℕ) → AbstractOracleMachine

abstractOracleMachineEquiv : AbstractOracleMachine ≃ ℕ ⊎ (ℕ × ℕ)
abstractOracleMachineEquiv = isoToEquiv (iso f g f-g g-f)
  where
    f : AbstractOracleMachine → ℕ ⊎ (ℕ × ℕ)
    f (returnValue n) = inl n
    f (queryAndContinue n e) = inr (n , e)

    g : ℕ ⊎ (ℕ × ℕ) → AbstractOracleMachine
    g (inl n) = returnValue n
    g (inr (n , e)) = queryAndContinue n e

    f-g : (x : ℕ ⊎ (ℕ × ℕ)) → f (g x) ≡ x
    f-g (inl x) = refl
    f-g (inr x) = refl

    g-f : (x : AbstractOracleMachine) → g (f x) ≡ x
    g-f (returnValue n) = refl
    g-f (queryAndContinue n e) = refl

instance
  aomSCounted : StrictlyCounted AbstractOracleMachine
  aomSCounted = sCtdFromEquiv abstractOracleMachineEquiv

data HaltingTime : Type where
  now : HaltingTime
  later : (n : ℕ) → (t : HaltingTime) → HaltingTime

haltingTime→list : HaltingTime → List ℕ
haltingTime→list now = []
haltingTime→list (later n t) = n ∷ haltingTime→list t

list→haltingTime : List ℕ → HaltingTime
list→haltingTime [] = now
list→haltingTime (n ∷ t) = later n (list→haltingTime t)

haltingTimeListEquiv : HaltingTime ≃ (List ℕ)
haltingTimeListEquiv = isoToEquiv (iso f g f-g g-f)
  where
    f : HaltingTime → List ℕ
    f now = []
    f (later n x) = n ∷ f x 

    g : List ℕ → HaltingTime
    g [] = now
    g (n ∷ x) = later n (g x)

    f-g : (l : List ℕ) → f (g l) ≡ l
    f-g [] = refl
    f-g (x ∷ l) = cong (x ∷_ ) (f-g l)

    g-f : (t : HaltingTime) → g (f t) ≡ t
    g-f now = refl
    g-f (later n t) = cong (later n) (g-f t)

instance
  htSCounted : StrictlyCounted HaltingTime
  htSCounted = sCtdFromEquiv haltingTimeListEquiv
