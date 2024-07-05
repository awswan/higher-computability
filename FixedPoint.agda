open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection
open import Cubical.Relation.Nullary
open import CubicalExtras.Relation.Nullary.Properties
open import Cubical.HITs.PropositionalTruncation

open import Types.PropNegNeg

open import Dominance.Base
open import Dominance.DoubleNegation

open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.PropositionalTruncation
open import Notation.CoercesToType
open import Notation.Variables

module FixedPoint
  where

module Fixed {A : Type ℓ}
  {B : Type ℓ'}
  (_⊑_ : B → B → Type ℓ'')
  (s : A → (A → B))
  (sDense : (f : A → B) → ∥ Σ[ a₀ ∈ A ] ((a : A) → f a ⊑ s a₀ a) ∥₁)
  (F : B → B)
  where
  t : A → B
  t a = F (s a a)

  fixed : ∥ Σ[ b ∈ B ] F b ⊑ b ∥₁
  fixed = map (λ (a₀ , p) → (s a₀ a₀) , (p a₀)) (sDense t)

  ifMaximal : ((b b' : B) → F b ⊑ b' → F b ≡ b') → ∥ Σ[ b ∈ B ] F b ≡ b ∥₁
  ifMaximal maxF = map (λ (a₀ , p) → (s a₀ a₀) , (maxF _ _ (p a₀))) (sDense t)

-- _⊑_ : {A : Type ℓa} {B : Type ℓb}
--   {Dom : PreDominance ℓ ℓ'} → (A → ∂ Dom B) →
--   (A → ∂ Dom B) → Type (ℓ-max (ℓ-max ℓa ℓb) ℓ)
-- _⊑_ {A = A} {B = B} f g = (a : A) → f a ↓= b ⇒ (g a ↓= c & (c ≡ b))



mvFixed : {A : Type ℓa}
  (sepA : Separated A)
  (s : A → (A → ∂¬¬ ℓ A))
  (sMultiDense :
    (R : A → A → hProp¬¬ (ℓ-max ℓa ℓ)) →
    ((a : A) → NonEmpty (Σ[ b ∈ A ] ⟨ R a b ⟩) → ∥ Σ[ b ∈ A ] ⟨ R a b ⟩ ∥₁) →
    ∥ Σ[ e ∈ A ] ((a : A) → NonEmpty (Σ[ b ∈ A ] ⟨ R a b ⟩) → s e a ↓= b & ⟨ R a b ⟩) ∥₁ )
  (F : A → A → ∂¬¬ ℓ A) →
  ∥ Σ[ e ∈ A ] F e ⊑ s e ∥₁

mvFixed {ℓa = ℓa} {ℓ = ℓ} {A = A} sepA s sMultiDense F = {!!}
  where
    R : A → A → hProp¬¬ (ℓ-max ℓa ℓ)
    hProp¬¬.P (R a b) = (c : A) → s a a ↓= d ⇒ (F d c ↓= e ⇒ (s b c ↓= f & (f ≡ e)))
    hProp¬¬.isPropP (R a b) =
      isPropΠ3 (λ c _ e → isPropΣ (isPropDomain (s b c)) λ _ → Separated→isSet sepA _ _)
    hProp¬¬.StableP (R a b) =
      StableΠ (λ c → StableΠ (λ _ → StableΠ λ x → 
        isDefinedAndStable (s b c) λ d → sepA d (value (F _ _) x)))

    totalR : (a : A) → ∥ Σ[ b ∈ A ] ⟨ R a b ⟩ ∥₁
    totalR a = do
      (b , bWorks) ← sMultiDense R' R'total
      return (b , (λ c y z → {!!} , {!!}))
      where
        R' : A → A → hProp¬¬ (ℓ-max ℓa ℓ)
        hProp¬¬.P (R' c f) = s a a ↓= d & (F d c ↓= e & (f ≡ e))
        hProp¬¬.isPropP (R' c f) =
          isPropΣ (isPropDomain (s a a))
                  (λ x → isPropΣ (isPropDomain (F (value (s a a) x) c))
                  λ _ → Separated→isSet sepA _ _)
        hProp¬¬.StableP (R' c f) = isDefinedAndStable (s a a)
          λ d → isDefinedAndStable (F d c) λ e → sepA f e
        
        R'total : (c : A) → NonEmpty (Σ[ f ∈ A ] ⟨ R' c f ⟩) → ∥ Σ[ f ∈ A ] ⟨ R' c f ⟩ ∥₁
        R'total c ¬¬fr = ∣ (value (F d c) (snd bothDefd)) ,
                           (fst bothDefd) , ((snd bothDefd) , refl) ∣₁
          where
            bothDefd : s a a ↓= d & (F d c ↓)
            bothDefd = isDefinedAndStable (s a a) (λ d → ∂¬¬domainStable (F d c))
                                          (¬¬map (λ (f , (x , (y , _))) → (x , y)) ¬¬fr)

            d = value (s a a) (fst bothDefd)

    -- open PreDominance (¬¬PreDom ℓ)
    -- diag : A → A → ∂¬¬ ℓ A
    -- diag e n = s e e >>= λ d → F d n  

    -- R : A → A → hProp¬¬ (ℓ-max ℓa ℓ)
    -- hProp¬¬.P (R e n) = diag e ⊑ s n
    -- hProp¬¬.StableP (R e n) =
    --   StableΠ λ a →
    --     StableΠ (λ _ →
    --       StableΣ (∂domainStable (s n a)) (isPropDomain (s n a)) λ _ → sepA _ _)
    -- hProp¬¬.isPropP (R e n) =
    --   isPropΠ (λ a →
    --     isPropΠ (λ _ →
    --       isPropΣ (isPropDomain (s n a)) λ _ → Separated→isSet sepA _ _))

    -- total : (e : A) →
    --   ∥ Σ[ diagCode ∈ A ] ((e : A) → s diagCode e ↓= a & (diag e ⊑ s a))  ∥₁
    -- total e = do
    --   return {!!}
    --   where
    --     S : A → A → hProp¬¬ (ℓ-max ℓa ℓ)
    --     hProp¬¬.P (S n a) = diag e n ↓= d ⇒ (a ≡ d)
    --     hProp¬¬.isPropP (S n a) = isPropΠ (λ S → Separated→isSet sepA _ _)
    --     hProp¬¬.StableP (S n a) = StableΠ (λ _ → sepA _ _)

    --     totalS : (e : A) → ∥ Σ[ b ∈ A ] ⟨ S e b ⟩ ∥₁
    --     totalS e = do
    --       (a , p) ← sMultiDense S {!!}
    --       {!!}
    --       where
    --         isDiage : A → A → hProp¬¬ {!!}
    --         hProp¬¬.P (isDiage a b) = diag e a ↓= c & (b ≡ c)
