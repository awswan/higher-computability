open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.List.FinData
open import Cubical.Data.List.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.FinData.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Isomorphism

module CubicalExtras.Data.List.FinData where

open Iso

lookup-tabulate-iso : (A : Type ℓ) → Iso (List A) (Σ[ n ∈ ℕ ] (Fin n → A))
fun (lookup-tabulate-iso A) xs = (length xs) , lookup xs
inv (lookup-tabulate-iso A) (n , f) = tabulate n f
leftInv (lookup-tabulate-iso A) = tabulate-lookup
rightInv (lookup-tabulate-iso A) (n , f) =
  ΣPathP ((length-tabulate n f) , lookup-tabulate n f)

lookup-tabulate-equiv : (A : Type ℓ) → List A ≃ (Σ[ n ∈ ℕ ] (Fin n → A))
lookup-tabulate-equiv A = isoToEquiv (lookup-tabulate-iso A)
