{-# OPTIONS --cubical --guardedness #-} --safe

open import itree
open import M
open import Coalg

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Prod

open import Cubical.Codata.Stream

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.FunExtEquiv

open import Cubical.HITs.SetQuotients

open import Container
open import helper

module bisim-examples where

-------------------------------
-- The identity bisimulation --
-------------------------------

Δ : ∀ {ℓ} {S : Container {ℓ}} -> bisimulation S M-coalg (_≡_)
αᵣ (Δ {S = S}) (a , b , r) = fst (out-fun a) , (λ x → snd (out-fun a) x , (snd (out-fun a) x , refl {x = snd (out-fun a) x}))
rel₁ (Δ {S = S}) = funExt λ {(a , b , r) → refl {x = out-fun a}}
rel₂ (Δ {S = S}) = funExt λ {(a , b , r) → cong (out-fun) (sym r)}

---------------------------------------------
-- Strong Bisimulation for the delay monad --
---------------------------------------------

mutual
  data _∼_ {R} : (x y : delay R) → Set where
    ∼now   : ∀ {r} → delay-ret r ∼ delay-ret r
    ∼later : ∀ {x y} → x ∞∼ y → (delay-tau x) ∼ (delay-tau y)

  record _∞∼_ {R} (x y : delay R) : Set where
    coinductive
    field
      force : x ∼ y

open _∞∼_ public

delay-bisim : ∀ {R} → bisimulation (delay-S R) M-coalg _∼_
αᵣ (delay-bisim) (a , b , ∼now {r}) = inr r , λ ()
αᵣ (delay-bisim) (a , b , ∼later {x} {y} p) = inl tt , λ _ → x , y , force p
rel₁ (delay-bisim) i (a , b , (∼now {r})) = out-inverse-in i (inr r , λ ())
rel₁ (delay-bisim) i (a , b , (∼later {x} {y} p)) = out-inverse-in i (inl tt , λ _ → x)
rel₂ (delay-bisim) i (a , b , (∼now {r})) = out-inverse-in i (inr r , λ ())
rel₂ (delay-bisim) i (a , b , (∼later {x} {y} p)) = out-inverse-in i (inl tt , λ _ → y)

delay-coinduction : ∀ {R} {m m'} → m ∼ m' → m ≡ m'
delay-coinduction {R} = coinduction (_∼_ {R}) delay-bisim

-------------------------------------------
-- Weak Bisimulation for the delay monad --
-------------------------------------------

record _≈_ {R} (x y : delay R) : Set where
  coinductive
  field
    sim : x ∼ y
    rel : ∀ (x : delay R) → x ≡ delay-tau x

open _≈_

weak-delay-coinduction : ∀ {R} {m m' : delay R} → m ≈ m' → m ≡ m'
weak-delay-coinduction {R} p = delay-coinduction (sim p)

-----------------------------------------------
-- Delay Set-Quotiented by Weak Bisimulation --
-----------------------------------------------

delay-set-quotiented : ∀ R → Set
delay-set-quotiented R = (delay R) / (_≈_ {R}) -- equality by eq/

----------------------
-- Partiality monad --
----------------------

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
