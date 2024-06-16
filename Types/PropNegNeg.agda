open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open import Cubical.Functions.Embedding

open import Cubical.Reflection.StrictEquiv

open import Notation.CoercesToType
open import Notation.Variables

module Types.PropNegNeg where

record hProp¬¬ (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    P : Type ℓ
    isPropP : isProp P
    StableP : Stable P

module _ {ℓ : Level} where
  hProp¬¬AsΣ : hProp¬¬ ℓ ≃ (Σ[ P ∈ Type ℓ ] (isProp P × Stable P))
  unquoteDef hProp¬¬AsΣ =
    defStrictEquiv hProp¬¬AsΣ
      (λ x → (hProp¬¬.P {ℓ = ℓ} x)
        , ((hProp¬¬.isPropP x) , (hProp¬¬.StableP x)))
      λ (P , (propP , stabP)) →
        record { P = P
               ; isPropP = propP
               ; StableP = stabP }

hProp¬¬isEmbedP : {ℓ : Level} → isEmbedding (hProp¬¬.P {ℓ = ℓ})
hProp¬¬isEmbedP =
  isEmbedding-∘
    (λ u v → isEmbeddingFstΣProp (λ _ → isPropΣ isPropIsProp
                                                (λ p → isProp→ p)))
    (isEquiv→isEmbedding (snd hProp¬¬AsΣ))

instance
  hProp¬¬ToType : CoercesToType (hProp¬¬ ℓ) ℓ
  CoercesToType.getType hProp¬¬ToType = hProp¬¬.P
