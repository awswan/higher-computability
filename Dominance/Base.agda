open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat

open import Cubical.Functions.Embedding

open import Cubical.Data.Unit

open import Notation.Variables
open import Notation.ModalOperatorSugar

module Dominance.Base where

-- proof relevant version of dominance
record PreDominance (ℓ ℓ' : Level) :
  Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    inDom : Type ℓ → Type ℓ'
    onlyProps : (A : Type ℓ) → inDom A → isProp A
    containsUnit : inDom Unit*
    Σclosed : {P : Type ℓ} → {Q : P → Type ℓ} →
      inDom P → ((p : P) → inDom (Q p)) →
      inDom (Σ P Q)

open PreDominance

record ∂ (D : PreDominance ℓ ℓ') (A : Type ℓ'') :
  Type (ℓ-max ℓ'' (ℓ-max (ℓ-suc ℓ) ℓ')) where
  field
    _↓ : Type ℓ
    domainInD : PreDominance.inDom D _↓
    value : _↓ → A

open ∂ public

module _ {ℓa : Level} {D : PreDominance ℓ ℓ'} {A : Type ℓa} where
  isPropDomain : (α : ∂ D A) → isProp (α ↓)
  isPropDomain α = onlyProps D (α ↓) (domainInD α)
  
  isDefinedAnd : (α : ∂ D A) → (Z : A → Type ℓ'') → Type (ℓ-max ℓ ℓ'')
  isDefinedAnd α Z = Σ[ d ∈ α ↓ ] Z (∂.value α d)

  isDefinedImplies : (α : ∂ D A) → (Z : A → Type ℓ'') → Type (ℓ-max ℓ ℓ'')
  isDefinedImplies α Z = (d : α ↓) → Z (∂.value α d)

  infixr 2 isDefinedAnd
  syntax isDefinedAnd α (λ x → Z) = α ↓= x & Z
  infixr 1 isDefinedImplies
  syntax isDefinedImplies α (λ x → Z) = α ↓= x ⇒ Z

  ↓=&hLevel : (n : HLevel) (α : ∂ D A) {Z : A → Type ℓ''} →
    ((a : A) → isOfHLevel (suc n) (Z a)) →
    isOfHLevel (suc n) (α ↓= a & Z a)
  ↓=&hLevel n α l =
    isOfHLevelΣ _ (isProp→isOfHLevelSuc n (PreDominance.onlyProps D (α ↓) (domainInD α)))
                λ d → l (value α d)

open ModalOperator

instance
  ∂Bind : {Pred : PreDominance ℓ ℓ'} →
    ModalOperator (ℓ-max (ℓ-suc ℓ) ℓ') (∂ Pred)
  _↓ (_>>=_ ∂Bind α f) = α ↓= z & (f z ↓)
  domainInD (_>>=_ (∂Bind {Pred = Pred}) α f) =
    Σclosed Pred (domainInD α) λ d → domainInD (f (value α d))
  value (_>>=_ ∂Bind α f) (α↓ , fα↓) = value (f (value α α↓)) fα↓
  _↓ (return ∂Bind a) = Unit*
  domainInD (return (∂Bind {Pred = Pred}) a) = containsUnit Pred
  value (return (∂Bind) b) _ = b

_⊑_ : {A : Type ℓa} {B : Type ℓb}
  {Dom : PreDominance ℓ ℓ'} {Dom' : PreDominance ℓ'' ℓ'''} → (B → ∂ Dom A) →
  (B → ∂ Dom' A) → Type (ℓ-max (ℓ-max (ℓ-max ℓa ℓ) ℓb) ℓ'')
_⊑_ {B = B} f g = (b : B) → f b ↓= a ⇒ (g b ↓= c & (c ≡ a))
