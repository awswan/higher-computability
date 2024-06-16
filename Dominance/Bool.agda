open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Dominance.Base

open import Notation.Variables

module Dominance.Bool where

BoolPred : PreDominance
PreDominance.Idx BoolPred = Bool
PreDominance.P BoolPred = Bool→Type
PreDominance.isPropP BoolPred = isProp-Bool→Type

∂dec : Type ℓ → Type ℓ
∂dec = ∂Pred BoolPred

BoolDom : Dominance
Dominance.pred BoolDom = BoolPred
Dominance.isEmbeddingP BoolDom b b' =
  snd (propBiimpl→Equiv
      (isSetBool _ _)
      (isOfHLevel≡ 1 (isProp-Bool→Type b) (isProp-Bool→Type b'))
      (cong Bool→Type)
      λ p → Bool→TypeInj b b' (pathToEquiv p))
Dominance.ΣLift BoolDom false b' = false
Dominance.ΣLift BoolDom true b' = b' tt
Dominance.ΣLiftIsΣ BoolDom {false} {b'} = ua (uninhabEquiv (λ x → x) fst)
Dominance.ΣLiftIsΣ BoolDom {true} {b'} = sym (ua (ΣUnit (Bool→Type ∘ b')))
