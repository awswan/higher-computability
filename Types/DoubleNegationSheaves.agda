open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Data.Bool
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties

open import Cubical.Data.Empty

open import Cubical.HITs.Nullification renaming (rec to nullRec)

open import Types.PropNegNeg

open import Notation.CoercesToType
open import Notation.Variables

module Types.DoubleNegationSheaves where

DenseProps : (ℓ : Level) → Σ[ P ∈ hProp ℓ ] ¬ ¬ (fst P) → Type ℓ
DenseProps ℓ = fst ∘ fst

∇ : Type ℓ' → Type (ℓ-max ℓ' (ℓ-suc ℓ))
∇ {ℓ = ℓ} = Null (DenseProps ℓ)

Sheaf : Type ℓ' → Type (ℓ-max ℓ' (ℓ-suc ℓ))
Sheaf {ℓ = ℓ} = isNull (DenseProps ℓ)

open isPathSplitEquiv

PropSheaf→Stable : {A : Type ℓ} → isProp A → Sheaf A → Stable A
PropSheaf→Stable {A = A} propA shfA ¬¬A =
  fst (sec (shfA ((A , propA) , ¬¬A))) (λ x → x)

StableProp→Sheaf : {A : Type ℓ'} → Stable A → isProp A → Sheaf {ℓ = ℓ} A
StableProp→Sheaf stableA propA P =
  fromIsEquiv _ (snd (propBiimpl→Equiv propA (isProp→ propA)
    (λ a _ → a) (λ f → stableA (¬¬map f (snd P)))))

∇→¬¬ : {A : Type ℓa} → ∇ {ℓ = ℓ} A → ¬ ¬ A
∇→¬¬ = nullRec (StableProp→Sheaf Stable¬ (isPropΠ (λ _ → isProp⊥))) ¬¬in

separatedEmbedsIn∇ : {A : Type ℓa} → Separated A →
  isEmbedding {A = A} {B = ∇ {ℓ = ℓ} A} ∣_∣
separatedEmbedsIn∇ {ℓ = ℓ} sepA a b =
  snd (propBiimpl→Equiv (setA a b)
      (topPreservesHLevel (fst ∘ fst) (snd ∘ fst) 2 setA ∣ a ∣ ∣ b ∣) (cong ∣_∣)
                          λ p → sepA a b
                            (∇→¬¬ (topUnitWeaklyInj (fst ∘ fst) (snd ∘ fst) a b p)))
  where
    setA = Separated→isSet sepA

separated→isInj∇unit : {ℓ : Level} {A : Type ℓa} → Separated A →
  (a b : A) → ∣ a ∣ ≡ ∣ b ∣ → a ≡ b
separated→isInj∇unit {ℓ = ℓ} sepA = isEmbedding→Inj (separatedEmbedsIn∇ {ℓ = ℓ} sepA)

_⇓ : {A : Type ℓa} → ∇ {ℓ = ℓ} A → Type (ℓ-max ℓa (ℓ-suc ℓ))
α ⇓ = fiber ∣_∣ α

Dec⇓ : (P : hProp¬¬ ℓ) →
  Σ[ β ∈ ∇ {ℓ = ℓ} Bool ] (Dec ⟨ P ⟩ ≃ β ⇓)
Dec⇓ P = β , (propBiimpl→Equiv (isPropDec propP) (isEmbedding→hasPropFibers (separatedEmbedsIn∇ separatedBool) β) (λ x → (Dec→Bool x) , (sym (fib x))) fiberToDec)
  where
    f : Dec ⟨ P ⟩ → ∇ Bool
    f x = ∣ Dec→Bool x ∣

    propP = hProp¬¬.isPropP P

    β : ∇ Bool
    β = hub (((Dec ⟨ P ⟩) , isPropDec propP) ,
                   λ w → w (no (λ p → w (yes p))))
            f
    fib : (p : Dec ⟨ P ⟩) → β ≡ f p
    fib p = spoke ((Dec ⟨ P ⟩ , isPropDec propP) , λ w → w (no (λ p → w (yes p))))
      f p

    fiberToDec : fiber ∣_∣ β → Dec ⟨ P ⟩
    fiberToDec (false , p) = no λ q →
      false≢true (separated→isInj∇unit separatedBool _ _ (p ∙ fib (yes q)))
    fiberToDec (true , p) = yes
      (hProp¬¬.StableP P (λ ¬q →
        true≢false (separated→isInj∇unit separatedBool _ _ (p ∙ fib (no ¬q)))))
