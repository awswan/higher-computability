open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.Reflection.StrictEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification.Properties
open import Types.DoubleNegationSheaves
open import Types.PropNegNeg

open import Notation.Variables
open import Notation.CoercesToType
open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.DoubleNegation

module Types.NablaZero where

record ∇₀ (A : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    isThis : A → hProp¬¬ (ℓ-max ℓ ℓ')
    wellDefd : (a a' : A) → ⟨ isThis a ⟩ →
      ⟨ isThis a' ⟩ → NonEmpty (a ≡ a')
    almostInh : NonEmpty (Σ[ a ∈ A ] ⟨ isThis a ⟩)

open ∇₀

module _ {ℓ' : Level} (A : Type ℓ) where 
  ∇₀asΣ : 
    (∇₀ {ℓ' = ℓ'} A) ≃
      (Σ[ P ∈ (A → hProp¬¬ (ℓ-max ℓ ℓ')) ]
        ((a a' : A) → ⟨ P a ⟩ → ⟨ P a' ⟩ → NonEmpty (a ≡ a')) ×
      NonEmpty (Σ[ a ∈ A ] ⟨ P a ⟩))
  unquoteDef ∇₀asΣ = defStrictEquiv ∇₀asΣ
    (λ α → (isThis {ℓ' = ℓ'} {A = A} α) , (wellDefd α , almostInh α))
    λ (it , (wd , ai)) → record { isThis = it ; wellDefd = wd ; almostInh = ai }

∇₀-η : {A : Type ℓ} → A → ∇₀ {ℓ' = ℓ'} A
isThis (∇₀-η {ℓ' = ℓ'} {A = A} a) b = NonEmpty→hProp¬¬ (Lift {j = ℓ'} (a ≡ b))
∇₀.wellDefd (∇₀-η a) b c ¬¬p ¬¬q = do
  (lift p) ← ¬¬p
  (lift q) ← ¬¬q
  return (sym p ∙ q)
∇₀.almostInh (∇₀-η a) = return (a , return (lift refl))

separated∇₀ : Separated (∇₀ {ℓ' = ℓ'} A)
separated∇₀ {A = A} α β ¬¬p = invEq e
  (Σ≡Prop (λ α → isProp× (isPropΠ4 (λ _ _ _ _ → isProp¬ _)) (isProp¬ _))
    (funExt (λ a → separatedHProp¬¬ _ _ (¬¬map (cong (λ α → isThis α a)) ¬¬p))))
  where
    e : (α ≡ β) ≃ (equivFun (∇₀asΣ A) α ≡ equivFun (∇₀asΣ A) β)
    e = congEquiv (∇₀asΣ A)

isSet∇₀ : isSet (∇₀ {ℓ' = ℓ'} A)
isSet∇₀ = Separated→isSet separated∇₀

∇₀≡ : {α β : ∇₀ {ℓ' = ℓ'} A} → ((a : A) → isThis α a ≡ isThis β a) → α ≡ β
∇₀≡ {A = A} {α} {β} p =
  invEq e (Σ≡Prop (λ x → isProp× (isPropΠ4 λ _ _ _ _ → isProp¬ _) (isProp¬ _)) (funExt p))
  where
    e  = congEquiv (∇₀asΣ A)

injective∇₀ : (P : Type ℓ') (propP : isProp P)→ NonEmpty P →
  hasSection (const {A = ∇₀ {ℓ' = ℓ'} A} {B = P})
∇₀.isThis (fst (injective∇₀ P propP ¬¬P) f) a = Π¬¬ P (λ p → isThis (f p) a)
∇₀.wellDefd (fst (injective∇₀ P propP ¬¬P) f) a b x y =
  ¬¬P >>= λ p → wellDefd (f p) a b (x p) (y p)
∇₀.almostInh (fst (injective∇₀ P propP ¬¬P) f) = do
  p ← ¬¬P
  (a , x) ← ∇₀.almostInh (f p)
  return (a , λ q → subst (λ p' → ⟨ isThis (f p') a ⟩) (propP p q) x)
snd (injective∇₀ P propP ¬¬P) f =
  funExt (λ p → ∇₀≡ (λ a → hProp¬¬≡ (ua (Π-contractDom (inhProp→isContr p propP)))))

Sheaf∇₀ : Sheaf {ℓ = ℓ'} (∇₀ {ℓ' = ℓ'} A)
Sheaf∇₀ {A = A} =
  SeparatedAndInjective→Null (∇₀ A)
    (λ α β → StableProp→Sheaf (separated∇₀ α β) (isSet∇₀ α β))
    λ (P , ¬¬P) → injective∇₀ (fst P) (snd P) ¬¬P
