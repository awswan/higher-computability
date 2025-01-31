open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Nullary
open import Cubical.Reflection.StrictEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.HITs.Nullification
open import Cubical.HITs.PropositionalTruncation renaming (rec to truncRec)
open import Types.DoubleNegationSheaves
open import Types.PropNegNeg

open import Notation.Variables
open import Notation.CoercesToType
open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.DoubleNegation

open import Util.DoubleNegation
open import Util.Nullification

module Types.NablaZero where

record ∇₀ (A : Type ℓa) : Type (ℓ-max ℓa (ℓ-suc ℓ)) where
  field
    isThis : A → hProp¬¬ ℓ
    wellDefd : (a a' : A) → ⟨ isThis a ⟩ →
      ⟨ isThis a' ⟩ → NonEmpty (a ≡ a')
    almostInh : NonEmpty (Σ[ a ∈ A ] ⟨ isThis a ⟩)

open ∇₀

module _ {ℓ' : Level} (A : Type ℓ) where 
  ∇₀asΣ : 
    (∇₀ A) ≃
      (Σ[ P ∈ (A → hProp¬¬ ℓ') ]
        ((a a' : A) → ⟨ P a ⟩ → ⟨ P a' ⟩ → NonEmpty (a ≡ a')) ×
      NonEmpty (Σ[ a ∈ A ] ⟨ P a ⟩))
  unquoteDef ∇₀asΣ = defStrictEquiv ∇₀asΣ
    (λ α → (isThis {ℓ = ℓ'} {A = A} α) , (wellDefd α , almostInh α))
    λ (it , (wd , ai)) → record { isThis = it ; wellDefd = wd ; almostInh = ai }

∇₀unit : {A : Type ℓa} → A → ∇₀ {ℓ = ℓ-max ℓa ℓ} A
isThis (∇₀unit {ℓ = ℓ} {A = A} a) b = NonEmpty→hProp¬¬ (Lift {j = ℓ} (a ≡ b))
∇₀.wellDefd (∇₀unit a) b c ¬¬p ¬¬q = do
  (lift p) ← ¬¬p
  (lift q) ← ¬¬q
  return (sym p ∙ q)
∇₀.almostInh (∇₀unit a) = return (a , return (lift refl))

separated∇₀ : Separated (∇₀ {ℓ = ℓ'} A)
separated∇₀ {A = A} α β ¬¬p = invEq e
  (Σ≡Prop (λ α → isProp× (isPropΠ4 (λ _ _ _ _ → isProp¬ _)) (isProp¬ _))
    (funExt (λ a → separatedHProp¬¬ _ _ (¬¬map (cong (λ α → isThis α a)) ¬¬p))))
  where
    e : (α ≡ β) ≃ (equivFun (∇₀asΣ A) α ≡ equivFun (∇₀asΣ A) β)
    e = congEquiv (∇₀asΣ A)

isSet∇₀ : isSet (∇₀ {ℓ = ℓ} A)
isSet∇₀ = Separated→isSet separated∇₀

∇₀≡Equiv : {α β : ∇₀ {ℓ = ℓ} A} → (α ≡ β) ≃ ((a : A) → isThis α a ≡ isThis β a)
∇₀≡Equiv {A = A} {α = α} {β = β} =
  α ≡ β ≃⟨ congEquiv (∇₀asΣ A) ⟩
  equivFun (∇₀asΣ A) α ≡ equivFun (∇₀asΣ A) β
    ≃⟨ invEquiv (Σ≡PropEquiv (λ P → isProp× (isPropΠ4 (λ _ _ _ _ → isProp¬ _))
                                            (isProp¬ _))) ⟩
  (λ a → isThis α a) ≡ (λ a → isThis β a) ≃⟨ invEquiv funExtEquiv ⟩
  ((a : A) → isThis α a ≡ isThis β a) ■

∇₀≡Equiv' : {α β : ∇₀ {ℓ = ℓ} A} → (α ≡ β) ≃ ((a : A) → ⟨ isThis α a ⟩ ≃ ⟨ isThis β a ⟩)
∇₀≡Equiv' = ∇₀≡Equiv ∙ₑ equivΠ (idEquiv _) (λ a → hProp¬¬≡Equiv' _ _)

∇₀≡ : {α β : ∇₀ {ℓ = ℓ} A} → ((a : A) → isThis α a ≡ isThis β a) → α ≡ β
∇₀≡ {A = A} {α} {β} = invEq ∇₀≡Equiv

∇₀∩→ : (α β : ∇₀ {ℓ = ℓ} A) (a : A) → ⟨ ∇₀.isThis α a ⟩ → ⟨ ∇₀.isThis β a ⟩ →
  (a' : A) → ⟨ ∇₀.isThis α a' ⟩ → ⟨ ∇₀.isThis β a' ⟩
∇₀∩→ α β a x y a' z =
  hProp¬¬.StableP
    (∇₀.isThis β a')
    (¬¬map (λ p → subst (λ a'' → ⟨ isThis β a'' ⟩) p y) (wellDefd α a a' x z))

∇₀∩≡ : (α β : ∇₀ {ℓ = ℓ'} A) (a : A) → ⟨ ∇₀.isThis α a ⟩ → ⟨ ∇₀.isThis β a ⟩ → α ≡ β
∇₀∩≡ α β a x y =
  ∇₀≡ (λ b → hProp¬¬≡' (∇₀∩→ α β a x y b) (∇₀∩→ β α a y x b))

injective∇₀ : (P : Type ℓ') (propP : isProp P)→ NonEmpty P →
  hasSection (const {A = ∇₀ {ℓ = ℓ'} A} {B = P})
∇₀.isThis (fst (injective∇₀ P propP ¬¬P) f) a = Π¬¬ P (λ p → isThis (f p) a)
∇₀.wellDefd (fst (injective∇₀ P propP ¬¬P) f) a b x y =
  ¬¬P >>= λ p → wellDefd (f p) a b (x p) (y p)
∇₀.almostInh (fst (injective∇₀ P propP ¬¬P) f) = do
  p ← ¬¬P
  (a , x) ← ∇₀.almostInh (f p)
  return (a , λ q → subst (λ p' → ⟨ isThis (f p') a ⟩) (propP p q) x)
snd (injective∇₀ P propP ¬¬P) f =
  funExt (λ p → ∇₀≡ (λ a → hProp¬¬≡ (ua (Π-contractDom (inhProp→isContr p propP)))))

Sheaf∇₀ : Sheaf {ℓ = ℓ'} (∇₀ {ℓ = ℓ'} A)
Sheaf∇₀ {A = A} =
  SeparatedAndInjective→Null (∇₀ A)
    (λ α β → StableProp→Sheaf (separated∇₀ α β) (isSet∇₀ α β))
    λ (P , ¬¬P) → injective∇₀ (fst P) (snd P) ¬¬P

open isPathSplitEquiv

module Rec {ℓa ℓ : Level} {A : Type ℓa} {B : Type ℓb}
  (_≈_ : B → B → Type (ℓ-max ℓa ℓ)) (≡Is≃ : (b b' : B) → (b ≡ b') ≃ (b ≈ b')) -- local smallness
  (Bset : isSet B) (Bshf : Sheaf {ℓ = ℓ-max ℓ ℓa} B) where

  private
    Bsep : Separated B
    Bsep b b' ¬¬p =
      fst (sec (isNull≡ Bshf
        ((b ≈ b' , isOfHLevelRespectEquiv 1 (≡Is≃ _ _) (Bset _ _)) ,
                   ¬¬map (equivFun (≡Is≃ _ _)) ¬¬p))) (invEq (≡Is≃ _ _))

    fib : (∇₀ {ℓ = ℓ-max ℓ ℓa} A) → Σ[ P ∈ hProp (ℓ-max ℓa ℓ) ] NonEmpty (fst P)
    fst (fst (fib α)) = ∥ Σ[ a ∈ A ] ⟨ isThis α a ⟩ ∥₁
    snd (fst (fib α)) = isPropPropTrunc
    snd (fib α) = ¬¬map ∣_∣₁ (almostInh α)

    fibToB : (f : A → B) (α : ∇₀ {ℓ = ℓ-max ℓ ℓa} A) → fst (fst (fib α)) → B
    fibToB f α = (λ z → fst (truncRec
      {P = Σ[ b ∈ B ] ∥ Σ[ a ∈ A ] (f a ≡ b) × ⟨ isThis α a ⟩ ∥₁}
      (λ (b , x) (b' , x') →
        Σ≡Prop (λ _ → isPropPropTrunc)
               (rec2 (Bset _ _)
                     (λ (a , (p , u)) (a' , (p' , u')) →
                           sym p ∙∙ Bsep _ _ (¬¬map (cong f) (wellDefd α a a' u u')) ∙∙ p') x x'))
      (λ (a , u) → (f a) , ∣ a , (refl , u) ∣₁) z))

  ∇₀rec : (f : A → B) → ∇₀ {ℓ = ℓ-max ℓ ℓa} A → B
  ∇₀rec f α = fst (sec (Bshf (fib α))) (fibToB f α)
    

  ∇₀recβ : (f : A → B) (a : A) → ∇₀rec f (∇₀unit {ℓ = ℓ-max ℓ ℓa} a) ≡ f a
  ∇₀recβ f a = funExt⁻ (snd (sec (Bshf (fib (∇₀unit a)))) (fibToB f (∇₀unit a)))
                     ∣ a , (¬¬in (lift refl)) ∣₁

  ∇₀recEquiv : isPathSplitEquiv (λ (g : ∇₀ A → B) → g ∘ ∇₀unit {ℓ = ℓ-max ℓ ℓa})

  fst (sec (∇₀recEquiv )) = ∇₀rec 
  snd (sec (∇₀recEquiv)) f = funExt (∇₀recβ f)
  fst (secCong (∇₀recEquiv) f g) p =
      funExt λ α → Bsep _ _ do
        (a , x) ← ∇₀.almostInh α
        let q = ∇₀∩≡ α (∇₀unit a) a x (¬¬in (lift refl))
        return (cong f q ∙∙ funExt⁻ p a ∙∙ cong g (sym q))
  snd (secCong (∇₀recEquiv) f g) r =
      isSet→ Bset (f ∘ ∇₀unit) (g ∘ ∇₀unit) _ r

∇→∇₀ : {ℓ : Level} {A : Type ℓa} → ∇ {ℓ = ℓ-max ℓa ℓ} A → ∇₀ {ℓ = ℓ-max ℓa ℓ} A
∇→∇₀ {ℓa = ℓa} {ℓ = ℓ} = rec Sheaf∇₀ (∇₀unit {ℓ = ℓ-max ℓa ℓ})

private
  retractCriterion : {A : Type ℓa} {B : Type ℓb} (f : A → B)
    (fdense : (b : B) → NonEmpty (fiber f b))
    (sepB : Separated B)
    (g h : B → B) →
    (H : (a : A) → g (f a) ≡ h (f a)) → (b : B) → g b ≡ h b
  retractCriterion f fdense sepB g h H b = sepB (g b) (h b)
    (¬¬map (λ (a , p) → sym (cong g p) ∙∙ H a ∙∙ cong h p) (fdense b))
  
  isoCriterion : {ℓc : Level} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
    (sepB : Separated B) (sepC : Separated C)
    (f : A → B) (fdense : (b : B) → NonEmpty (fiber f b))
    (g : A → C) (gdense : (c : C) → NonEmpty (fiber g c))
    (h : B → C) (k : C → B)
    (commh : (a : A) → h (f a) ≡ g a)
    (commk : (a : A) → k (g a) ≡ f a)
      → Iso B C
  Iso.fun (isoCriterion _ _ _ _ _ _ h _ _ _) = h
  Iso.inv (isoCriterion _ _ _ _ _ _ _ k _ _) = k
  Iso.leftInv (isoCriterion sepB _ f fdense _ _ h k commh commk) =
    retractCriterion f fdense sepB (k ∘ h) (idfun _)
      λ a → cong k (commh a) ∙ commk a
  Iso.rightInv (isoCriterion _ sepC _ _ g gdense h k commh commk) =
    retractCriterion g gdense sepC (h ∘ k) (idfun _)
      λ a → cong h (commk a) ∙ commh a

module _ {ℓa : Level} {ℓ : Level} {A : Type ℓa} (setA : isSet A) where
  open Rec {ℓ-max (ℓ-suc ℓa) (ℓ-suc ℓ)} {ℓa} {ℓ} {A} (λ α β → fst (∇SetCode {ℓ = ℓ} setA α β)) (∇SetCode≃ {ℓ = ℓ} setA) (topPreservesHLevel (DenseProps (ℓ-max ℓa ℓ)) (λ P → snd (fst P)) 2 setA) (isNull-Null (DenseProps (ℓ-max ℓa ℓ)))
  ∇₀→∇ : ∇₀ {ℓ = ℓ-max ℓa ℓ} A → ∇ {ℓ = ℓ-max ℓa ℓ} A
  ∇₀→∇ = ∇₀rec ∣_∣

  ∇≃∇₀ : ∇₀ {ℓ = ℓ-max ℓa ℓ} A ≃ ∇ {ℓ = ℓ-max ℓa ℓ} A
  ∇≃∇₀ = isoToEquiv
    (isoCriterion
      separated∇₀ (separated∇ {ℓ = ℓ} setA) (∇₀unit {ℓ = ℓ-max ℓa ℓ})
      (λ α → do
        (a , p) ← almostInh α
        ¬¬in (a , (∇₀∩≡ (∇₀unit a) α a (¬¬in (lift refl)) p)))
      ∣_∣ (λ α → ∇→¬¬ (nullFiber α)) ∇₀→∇ (∇→∇₀ {ℓ = ℓ-max ℓa ℓ})
      (∇₀recβ ∣_∣)
      λ a → refl)

sheafHProp¬¬ : Sheaf (hProp¬¬ ℓ)
sheafHProp¬¬ {ℓ = ℓ} =
  SeparatedAndInjective→Null (hProp¬¬ ℓ)
      (λ P Q → StableProp→Sheaf
        (λ ¬¬p → hProp¬¬≡ (hPropExt (hProp¬¬.isPropP P)
                 (hProp¬¬.isPropP Q)
                 (λ p → hProp¬¬.StableP Q (¬¬map (λ q → subst hProp¬¬.P q p) ¬¬p))
                 λ q → hProp¬¬.StableP P (¬¬map (λ p → subst hProp¬¬.P (sym p) q) ¬¬p)))
                 (isSetHProp¬¬ P Q))
      (λ x → isInjectiveHProp¬¬ (fst x) (snd x))

extendPredicate : {ℓa ℓ : Level} (A : Type ℓa) (P : A → hProp¬¬ (ℓ-max ℓ ℓa)) →
  ∇₀ {ℓ = ℓ-max ℓ ℓa} A → hProp¬¬ (ℓ-max ℓ ℓa)
extendPredicate A P α = Π¬¬ A (λ a → Π¬¬ ⟨ isThis α a ⟩ (λ _ → P a))

extendBinaryRelation : {ℓa ℓ : Level} (A : Type ℓa) (R : A → A → hProp¬¬ (ℓ-max ℓ ℓa)) →
  ∇₀ {ℓ = ℓ-max ℓ ℓa} A → ∇₀ {ℓ = ℓ-max ℓ ℓa} A → hProp¬¬ (ℓ-max ℓ ℓa)

extendBinaryRelation A R α β =
  Π¬¬ A (λ a → Π¬¬ A (λ b → Π¬¬ ⟨ isThis α a ⟩ (λ _ → Π¬¬ ⟨ isThis β b ⟩ (λ _ → R a b))))

_⇓₀ : {A : Type ℓa} → ∇₀ {ℓ = ℓ-max ℓ ℓa} A → Type (ℓ-max ℓ ℓa)
_⇓₀ {A = A} α = Σ[ a ∈ A ] ⟨ isThis α a ⟩
