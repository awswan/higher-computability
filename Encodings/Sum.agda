open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Nat.IsEven
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to ⊎rec)

module Encodings.Sum where

module OddEvenEquivM where
  f : ℕ ⊎ ℕ → ℕ
  f (inl n) = 2 · n
  f (inr n) = 1 + (2 · n)

  evenT→Path : (n : ℕ) → (isEvenT n) → (isEven n ≡ true)
  oddT→Path : (n : ℕ) → (isOddT n) → (isOdd n ≡ true)

  evenT→Path zero nEven = refl
  evenT→Path (suc n) nOdd = oddT→Path n nOdd

  oddT→Path (suc n) nEven = evenT→Path n nEven


  fEquiv : isEquiv f
  isEquiv.equiv-proof fEquiv n = ⊎rec ifEven ifOdd (evenOrOdd n)
    where
      ifEven : isEvenT n → isContr (fiber f n)
      ifEven nEven = ((inl (fst fib)) , (sym (snd fib))) ,
                     λ {(inl m , p) → Σ≡Prop (λ _ → isSetℕ _ _)
                       (cong inl (inj-sm· {m = 1} (sym (snd fib) ∙ sym p)))
                       ; (inr m , p) → ⊥rec (true≢false (sym (evenT→Path n nEven) ∙
                         falseIsEven n (m , (sym p))))}
        where
          fib : Σ[ m ∈ ℕ ] n ≡ (2 · m)
          fib = isEvenTrue n (evenT→Path n nEven)

      ifOdd : isOddT n → isContr (fiber f n)
      ifOdd nOdd = ((inr (fst fib)) , sym (snd fib)) ,
                 λ {(inl m , p) → ⊥rec (true≢false (sym (trueIsEven n (m , (sym p))) ∙
                   ¬IsOddTrue n (oddT→Path n nOdd)))
                 ; (inr m , p) → Σ≡Prop (λ _ → isSetℕ _ _)
                   (cong inr (inj-sm· {m = 1} (injSuc (sym (snd fib) ∙ sym p))))}
        where
          fib : Σ[ m ∈ ℕ ] n ≡ 1 + (2 · m)
          fib = isOddTrue n (oddT→Path n nOdd)

abstract
  oddEvenEquiv : ℕ ⊎ ℕ ≃ ℕ
  oddEvenEquiv = OddEvenEquivM.f , OddEvenEquivM.fEquiv
