open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Data.Bool
open import Cubical.HITs.PropositionalTruncation renaming (rec to truncRec)
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Properties

open import Cubical.Data.Empty hiding (rec)

open import Cubical.HITs.Nullification renaming (rec to nullRec ; elim to nullElim)

open import Types.PropNegNeg

open import Notation.CoercesToType
open import Notation.Variables

open import Util.DoubleNegation

module Types.DoubleNegationSheaves where

DenseProps : (ℓ : Level) → Σ[ P ∈ hProp ℓ ] ¬ ¬ (fst P) → Type ℓ
DenseProps ℓ = fst ∘ fst

∇ : Type ℓ' → Type (ℓ-max ℓ' (ℓ-suc ℓ))
∇ {ℓ = ℓ} = Null (DenseProps ℓ)

Sheaf : Type ℓ' → Type (ℓ-max ℓ' (ℓ-suc ℓ))
Sheaf {ℓ = ℓ} = isNull (DenseProps ℓ)

lowerSheaf : {A : Type ℓa} → Sheaf {ℓ = ℓ-max ℓ ℓ'} A → Sheaf {ℓ = ℓ} A
lowerSheaf {ℓ = ℓ} {ℓ' = ℓ'} {A = A} shfA (P , ¬¬P) = fromIsEquiv const (snd e)
  where
    e : A ≃ (fst P → A)
    e = A ≃⟨ const , (toIsEquiv const
                     (shfA ((Lift {j = ℓ'} (fst P) ,
                                  isOfHLevelLift 1 (snd P)) , ¬¬map lift ¬¬P))) ⟩
        (Lift (fst P) → A) ≃⟨ preCompEquiv LiftEquiv ⟩
        (fst P → A) ■

open isPathSplitEquiv

propSheaf→Stable : {A : Type ℓ} → isProp A → Sheaf A → Stable A
propSheaf→Stable {A = A} propA shfA ¬¬A =
  fst (sec (shfA ((A , propA) , ¬¬A))) (λ x → x)

setSheaf→Separated : {A : Type ℓa} → isSet A → Sheaf A → Separated A
setSheaf→Separated setA shfA a a' =
  propSheaf→Stable (setA a a') (isNull≡ shfA)

StableProp→Sheaf : {A : Type ℓ'} → Stable A → isProp A → Sheaf {ℓ = ℓ} A
StableProp→Sheaf stableA propA P =
  fromIsEquiv _ (snd (propBiimpl→Equiv propA (isProp→ propA)
    (λ a _ → a) (λ f → stableA (¬¬map f (snd P)))))

Sheaf⊥ : Sheaf {ℓ = ℓ} ⊥
Sheaf⊥ =
  StableProp→Sheaf (λ z → z (λ x → x)) isProp⊥

∇¬ : {A : Type ℓa} → ¬ A → ¬ (∇ {ℓ = ℓ} A)
∇¬ ¬a = nullRec Sheaf⊥ ¬a

∇→¬¬ : {A : Type ℓa} → ∇ {ℓ = ℓ} A → ¬ ¬ A
∇→¬¬ α ¬a = ∇¬ ¬a α

∇≃¬¬ : {A : Type ℓa} (propA : isProp A) → ∇ {ℓ = ℓ-max ℓ ℓa} A ≃ (¬ ¬ A)
∇≃¬¬ {ℓa} {ℓ = ℓ} {A = A} propA =
  propBiimpl→Equiv
    (NullPreservesProp propA) (isProp¬ _)
    ∇→¬¬
    λ ¬¬a → fst (sec (lowerSheaf {ℓ' = ℓ} (isNull-Null (DenseProps (ℓ-max ℓa ℓ))) ((A , propA) , ¬¬a))) ∣_∣

{- A kind of local smallness for ∇ A when A is a set.
-}
∇SetCode : {A : Type ℓa} (setA : isSet A) → ∇ {ℓ = ℓ-max ℓa ℓ} A → ∇ {ℓ = ℓ-max ℓa ℓ} A → NullType (DenseProps (ℓ-max ℓa ℓ)) {ℓ = ℓ}
∇SetCode {ℓa} {ℓ} setA =
  nullRec
    (isNullΠ (λ α → isNullNullTypes (DenseProps _) (snd ∘ fst) {ℓ = ℓ-max ℓa ℓ}))
    (λ a → nullRec (isNullNullTypes (DenseProps _) (snd ∘ fst) {ℓ = ℓ-max ℓa ℓ})
                   (λ b → NonEmpty (Lift {j = ℓ-max ℓ ℓa} (a ≡ b)) , isNullΠ (λ _ → Sheaf⊥)))

∇SetCode≃ : {A : Type ℓa} (setA : isSet A) → (α β : ∇ {ℓ = ℓ-max ℓa ℓ} A) →
  (α ≡ β) ≃ fst (∇SetCode {ℓ = ℓ} setA α β)
∇SetCode≃ {ℓa} {ℓ = ℓ} {A = A} setA =
  nullElim (λ α → isNullΠ (λ β → isNullEquiv (isNull≡ (isNull-Null (DenseProps _))) (e α β)))
    (λ a → nullElim (λ β → isNullEquiv (isNull≡ (isNull-Null (DenseProps _))) (e ∣ a ∣ β))
                    (λ b →
       ∣ a ∣ ≡ ∣ b ∣ ≃⟨ topUnitWeaklyEmb (DenseProps (ℓ-max ℓa ℓ)) (snd ∘ fst) a b ⟩
       ∇ (a ≡ b) ≃⟨ ∇≃¬¬ {ℓ = ℓ} (setA a b) ⟩
       NonEmpty (a ≡ b) ≃⟨ equiv→ (equiv→ LiftEquiv (idEquiv ⊥)) (idEquiv ⊥) ⟩
       NonEmpty (Lift (a ≡ b))
         ■))
    where
      e : (α β : ∇ A) → isNull (DenseProps (ℓ-max ℓa ℓ)) (fst (∇SetCode {ℓ = ℓ} setA α β))
      e α β = snd (∇SetCode {ℓ = ℓ} setA α β)

separated∇ : {A : Type ℓa} (setA : isSet A) → Separated (∇ {ℓ = ℓ-max ℓa ℓ} A)
separated∇ {ℓa = ℓa} {ℓ = ℓ} setA =
  nullElim
    (λ α → isNullΠ
      (λ β → isNullΠ (λ r → isNull≡ (isNull-Null (DenseProps (ℓ-max ℓa ℓ))))))
    (λ a → nullElim
      (λ β → isNullΠ (λ r → isNull≡ (isNull-Null (DenseProps (ℓ-max ℓa ℓ)))))
      (λ b r → ≡hub {α = ((Lift {j = ℓ} (a ≡ b)) , isOfHLevelLift 1 (setA a b)) ,
                     λ la≢lb →
                       r (λ p → ∇¬ (λ q → la≢lb (lift q))
                         (topUnitWeaklyInj (DenseProps (ℓ-max ℓ ℓa)) (snd ∘ fst) a b p))}
                  λ x → cong ∣_∣ (lower x)))

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
