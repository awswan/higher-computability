open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.Reflection.StrictEquiv

open import Cubical.Relation.Nullary.Base

open import Encodings.Product

open import Notation.CoercesToType

module Types.NatInf where

instance
  hitsOne : CoercesToType (ℕ → Bool) ℓ-zero
  CoercesToType.getType hitsOne f = Σ[ n ∈ ℕ ] Bool→Type (f n)

record ℕ∞ : Type where
  field
    f : ℕ → Bool
    unique : isProp ⟨ f ⟩

instance
  hitsOne' : CoercesToType ℕ∞ ℓ-zero
  CoercesToType.getType hitsOne' α = ⟨ ℕ∞.f α ⟩

ℕ→ℕ∞ : ℕ → ℕ∞
ℕ∞.f (ℕ→ℕ∞ n) m = Dec→Bool (discreteℕ m n)
ℕ∞.unique (ℕ→ℕ∞ n) (m , z) (m' , z') = Σ≡Prop (λ _ → isPropBool→Type) (p ∙ sym p')
  where
    p : m ≡ n
    p = DecBool→Dec (discreteℕ m n) z

    p' : m' ≡ n
    p' = DecBool→Dec (discreteℕ m' n) z'

ℕ→ℕ∞Ptd : (n : ℕ) → ⟨ ℕ→ℕ∞ n ⟩
ℕ→ℕ∞Ptd n = n , (Dec→DecBool (discreteℕ n n) refl)

ΣBool : (b : Bool) (c : (Bool→Type b) → Bool) → Bool
ΣBool false c = false
ΣBool true c = c tt

ΣBoolΣIso : {b : Bool} {c : (Bool→Type b) → Bool} →
  Iso (Bool→Type (ΣBool b c)) (Σ[ z ∈ Bool→Type b ] Bool→Type (c z))

Iso.fun (ΣBoolΣIso {true}) x = tt , x
Iso.inv (ΣBoolΣIso {true}) x = snd x
Iso.leftInv (ΣBoolΣIso {true}) _ = refl
Iso.rightInv (ΣBoolΣIso {true}) _ = refl

ΣBool≃Σ : {b : Bool} {c : (Bool→Type b) → Bool} →
  (Bool→Type (ΣBool b c)) ≃ (Σ[ z ∈ Bool→Type b ] Bool→Type (c z))
ΣBool≃Σ = isoToEquiv ΣBoolΣIso


module _ (α : ℕ∞) (β : ⟨ α ⟩ → ℕ∞) where
  private
    f : ℕ → Bool
    f n = let p = invEq ℕPairEquiv n in
      ΣBool (ℕ∞.f α (fst p)) λ x → ℕ∞.f (β ((fst p) , x)) (snd p)

    lemma : ⟨ f ⟩ ≃ (Σ[ x ∈ ⟨ α ⟩ ] ⟨ β x ⟩)
    lemma = 
      ⟨ f ⟩
        ≃⟨ idEquiv _ ⟩
      Σ[ n ∈ ℕ ] Bool→Type (f n)
        ≃⟨ Σ-cong-equiv-fst (invEquiv ℕPairEquiv) ⟩
      Σ[ (n , m) ∈ ℕ × ℕ ]
        Bool→Type (ΣBool (ℕ∞.f α n) λ x → ℕ∞.f (β (n , x)) m)
        ≃⟨ Σ-cong-equiv-snd (λ (n , m) → ΣBool≃Σ) ⟩
      Σ[ (n , m) ∈ ℕ × ℕ ]
        Σ[ x ∈ Bool→Type (ℕ∞.f α n) ] Bool→Type (ℕ∞.f (β (n , x)) m)
        ≃⟨ isoToEquiv rearrange ⟩
      Σ[ x ∈ ⟨ α ⟩ ] ⟨ β x ⟩ ■
        where
          rearrange :
            Iso
            (Σ[ (n , m) ∈ ℕ × ℕ ] Σ[ x ∈ Bool→Type (ℕ∞.f α n) ]
              Bool→Type (ℕ∞.f (β (n , x)) m))
            (Σ[ x ∈ ⟨ α ⟩ ] ⟨ β x ⟩)
          Iso.fun rearrange ((n , m) , x , y) = (n , x) , (m , y)
          Iso.inv rearrange ((n , x) , (m , y)) = (n , m) , (x , y)
          Iso.leftInv rearrange _ = refl
          Iso.rightInv rearrange _ = refl

  ℕ∞Σ : ℕ∞
  ℕ∞.f (ℕ∞Σ) = f
  ℕ∞.unique ℕ∞Σ =
    isOfHLevelRespectEquiv 1 (invEquiv lemma)
      (isPropΣ (ℕ∞.unique α) λ x → ℕ∞.unique (β x))

  ℕ∞Σ≃ : ⟨ ℕ∞Σ ⟩ ≃ (Σ[ x ∈ ⟨ α ⟩ ] ⟨ β x ⟩)
  ℕ∞Σ≃ = lemma
