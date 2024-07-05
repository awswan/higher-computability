open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import CubicalExtras.Relation.Nullary.Properties

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

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

hProp¬¬≡Equiv : (P Q : hProp¬¬ ℓ) → (P ≡ Q) ≃ (⟨ P ⟩ ≡ ⟨ Q ⟩)
hProp¬¬≡Equiv P Q =
  P ≡ Q
    ≃⟨ congEquiv hProp¬¬AsΣ ⟩
  equivFun hProp¬¬AsΣ P ≡ equivFun hProp¬¬AsΣ Q
    ≃⟨ invEquiv (Σ≡PropEquiv (λ P → isPropΣ isPropIsProp λ propP → isPropΠ (λ _ → propP))) ⟩
  ⟨ P ⟩ ≡ ⟨ Q ⟩ ■

isSetHProp¬¬ : isSet (hProp¬¬ ℓ)
isSetHProp¬¬ P Q = isOfHLevelRespectEquiv 1 (invEquiv (hProp¬¬≡Equiv P Q))
                                            (isOfHLevel≡ 1 (hProp¬¬.isPropP P) (hProp¬¬.isPropP Q))

hProp¬¬≡ : {P Q : hProp¬¬ ℓ} → (⟨ P ⟩ ≡ ⟨ Q ⟩) → P ≡ Q
hProp¬¬≡ {P = P} {Q = Q} = invEq (hProp¬¬≡Equiv P Q)

hProp¬¬≡' : {P Q : hProp¬¬ ℓ} → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩) → P ≡ Q
hProp¬¬≡' {P = P} {Q = Q} f g =
  hProp¬¬≡ (hPropExt (hProp¬¬.isPropP P) (hProp¬¬.isPropP Q) f g)

separatedHProp¬¬ : Separated (hProp¬¬ ℓ)
separatedHProp¬¬ P Q ¬¬P≡Q =
  hProp¬¬≡' (λ p → hProp¬¬.StableP Q (¬¬map (λ P≡Q → subst hProp¬¬.P P≡Q p) ¬¬P≡Q))
            (λ q → hProp¬¬.StableP P (¬¬map (λ P≡Q → subst hProp¬¬.P (sym P≡Q) q) ¬¬P≡Q))

isInjectiveHProp¬¬ :
  (P : hProp ℓ) → NonEmpty (fst P) → hasSection (const {A = hProp¬¬ ℓ} {B = fst P})
hProp¬¬.P (fst (isInjectiveHProp¬¬ P ¬¬P) f) =
  (p : fst P) → hProp¬¬.P (f p)
hProp¬¬.isPropP (fst (isInjectiveHProp¬¬ P ¬¬P) f) = isPropΠ (λ p → hProp¬¬.isPropP (f p))
hProp¬¬.StableP (fst (isInjectiveHProp¬¬ P ¬¬P) f) = StableΠ (λ p → hProp¬¬.StableP (f p))
snd (isInjectiveHProp¬¬ P ¬¬P) f =
  funExt (λ p → hProp¬¬≡ (ua (e p)))
  where
    e : (p : fst P) → ((p : fst P) → hProp¬¬.P (f p)) ≃ ⟨ f p ⟩
    e p =
      ((p : fst P) → hProp¬¬.P (f p))
        ≃⟨ invEquiv (equivΠ (invEquiv (isContr→≃Unit (inhProp→isContr p (snd P))))
                            (λ _ → idEquiv _)) ⟩
      (Unit → ⟨ f p ⟩) ≃⟨ ΠUnit _ ⟩
      ⟨ f p ⟩ ■

Σ¬¬ : (P : hProp¬¬ ℓ) → (Q : ⟨ P ⟩ → hProp¬¬ ℓ') → hProp¬¬ (ℓ-max ℓ ℓ')
hProp¬¬.P (Σ¬¬ P Q) = Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩
hProp¬¬.isPropP (Σ¬¬ P Q) = isPropΣ (hProp¬¬.isPropP P) (λ p → hProp¬¬.isPropP (Q p))
hProp¬¬.StableP (Σ¬¬ P Q) = StableΣ (hProp¬¬.StableP P) (hProp¬¬.isPropP P) (λ p → hProp¬¬.StableP (Q p))

Π¬¬ : (P : Type ℓ) (Q : P → hProp¬¬ ℓ') → hProp¬¬ (ℓ-max ℓ ℓ')
hProp¬¬.P (Π¬¬ P Q) = (p : P) → ⟨ Q p ⟩
hProp¬¬.isPropP (Π¬¬ P Q) = isPropΠ (λ p → hProp¬¬.isPropP (Q p))
hProp¬¬.StableP (Π¬¬ P Q) = StableΠ (λ p → hProp¬¬.StableP (Q p))

NonEmpty→hProp¬¬ : (P : Type ℓ) → hProp¬¬ ℓ
hProp¬¬.P (NonEmpty→hProp¬¬ P) = NonEmpty P
hProp¬¬.isPropP (NonEmpty→hProp¬¬ P) = isProp¬ _
hProp¬¬.StableP (NonEmpty→hProp¬¬ P) = Stable¬

Unit*¬¬ : hProp¬¬ ℓ
hProp¬¬.P Unit*¬¬ = Unit*
hProp¬¬.isPropP Unit*¬¬ = isPropUnit*
hProp¬¬.StableP Unit*¬¬ = λ _ → tt*
