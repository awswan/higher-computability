open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation

open import Types.PropNegNeg

open import Dominance.Base
open import Dominance.DoubleNegation

open import Notation.ModalOperatorSugar
open import Notation.ModalOpInstances.PropositionalTruncation
open import Notation.CoercesToType
open import Notation.Variables

open import Util.DoubleNegation

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

mvFixed : {A : Type ℓa}
  (sepA : Separated A)
  (s : A → (A → ∂¬¬ ℓ A))
  (sMultiDense :
    (R : A → A → hProp¬¬ (ℓ-max ℓa ℓ)) →
    ((a : A) → NonEmpty (Σ[ b ∈ A ] ⟨ R a b ⟩) → ∥ Σ[ b ∈ A ] ⟨ R a b ⟩ ∥₁) →
    ∥ Σ[ e ∈ A ] ((a : A) → NonEmpty (Σ[ b ∈ A ] ⟨ R a b ⟩) → s e a ↓= b & ⟨ R a b ⟩) ∥₁ )
  (F : A → A → ∂¬¬ ℓ A) →
  ∥ Σ[ e ∈ A ] F e ⊑ s e ∥₁

mvFixed {ℓa = ℓa} {ℓ = ℓ} {A = A} sepA s sMultiDense F =
  map (λ (e₀ , e₀Works) → fixedPt e₀ e₀Works) (sMultiDense R (λ a _ → totalR a))
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
      return (b , solves b bWorks)
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

        -- The value of the diagonal `F (s a a) c`, given proofs that both
        -- `s a a` and the subsequent application of `F` are defined.
        valAt : (c : A) → (Σ[ u ∈ s a a ↓ ] (F (value (s a a) u) c ↓)) → A
        valAt c (u , v) = value (F (value (s a a) u) c) v

        isPropBoth : (c : A) → isProp (Σ[ u ∈ s a a ↓ ] (F (value (s a a) u) c ↓))
        isPropBoth c =
          isPropΣ (isPropDomain (s a a)) λ u → isPropDomain (F (value (s a a) u) c)

        solves : (b : A) →
          ((c : A) → NonEmpty (Σ[ f ∈ A ] ⟨ R' c f ⟩) → s b c ↓= f & ⟨ R' c f ⟩) →
          ⟨ R a b ⟩
        solves b bWorks c y z =
          (fst sol) ,
          (snd (snd (snd sol)) ∙
            cong (valAt c) (isPropBoth c (fst (snd sol) , fst (snd (snd sol))) (y , z)))
          where
            sol = bWorks c (¬¬in (valAt c (y , z) , (y , (z , refl))))

    fixedPt : (e₀ : A) →
      ((a : A) → NonEmpty (Σ[ b ∈ A ] ⟨ R a b ⟩) → s e₀ a ↓= b & ⟨ R a b ⟩) →
      Σ[ e ∈ A ] F e ⊑ s e
    fixedPt e₀ e₀Works = value (s e₀ e₀) (fst sol) , λ c → snd sol c (fst sol)
      where
        sol : s e₀ e₀ ↓= b & ⟨ R e₀ b ⟩
        sol = e₀Works e₀ (∥∥₁→NonEmpty (totalR e₀))
