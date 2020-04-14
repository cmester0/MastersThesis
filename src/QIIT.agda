{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetQuotients

module QIIT where



record partiality-monad {A : Set} : Set₁ where
  field
    A⊥ : Set
    _⊑_ : A⊥ → A⊥ → Set

    η : A → A⊥
    ⊥ₐ : A⊥
    ⊔ : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)) → A⊥
    α : (x y : A⊥) → x ⊑ y → y ⊑ x → x ≡ y

    ⊑-refl : ∀ {x : A⊥} → x ⊑ x
    ⊑-trans : ∀ {x y z : A⊥} → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-⊥ : ∀ {x} → ⊥ₐ ⊑ x

    ⊑-prop : isProp ({x y : A⊥} → x ⊑ y)
    ⊑-0 : {(s , p) : Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)} → (n : ℕ) → s n ⊑ ⊔ (s , p)
    ⊑-1 : {(s , p) : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n))} → (x : A⊥) → (n : ℕ) → s n ⊑ x → ⊔ (s , p) ⊑ x

open partiality-monad

record partiality-algebra (A : Set) : Set₁ where
  field
    X : Set
    _⊑ₓ_ : X → X → Set
    ⊥ₓ : X
    ηₓ : A → X
    ⊔ₓ : (Σ (ℕ → X) λ s → (n : ℕ) → s n ⊑ₓ s (suc n)) → X

    ⊑ₓ-refl : ∀ {x : X} → x ⊑ₓ x
    ⊑ₓ-trans : ∀ {x y z : X} → x ⊑ₓ y → y ⊑ₓ z → x ⊑ₓ z
    ⊑ₓ-antisym : ∀ {x y : X} → x ⊑ₓ y → y ⊑ₓ x → x ≡ y
    ⊑ₓ-⊥ : ∀ {x} → ⊥ₓ ⊑ₓ x

    ⊑ₓ-prop : isProp ({x y : X} → x ⊑ₓ y)
    ⊑ₓ-0 : ((s , p) : Σ (ℕ → X) λ s → (n : ℕ) → s n ⊑ₓ s (suc n)) → (n : ℕ) → s n ⊑ₓ ⊔ₓ (s , p)
    ⊑ₓ-1 : ((s , p) : (Σ (ℕ → X) λ s → (n : ℕ) → s n ⊑ₓ s (suc n))) → (x : X) → (n : ℕ) → s n ⊑ₓ x → ⊔ₓ (s , p) ⊑ₓ x

open partiality-algebra

-- TODO : D(A)/∼D

ω-cpo : Set₁
ω-cpo = partiality-algebra ⊥ 

U : ω-cpo → Set
U x = X x

postulate
  F : Set → ω-cpo

U-partiality-algebra : ∀ x → partiality-algebra ⊥
U-partiality-algebra x = x


