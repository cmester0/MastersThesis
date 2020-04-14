{-# OPTIONS --cubical --guardedness #-} --safe

open import itree
open import M
open import Coalg
open import stream

open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Codata.Stream
open import Cubical.Data.Prod

open import Container

module bisim-stream where

----------------------------------------
-- The stream bisimulation Properties --
----------------------------------------

-- Bisimulation principle for streams
record stream≈ {A} (x y : stream A) : Set where
  coinductive
  field
    hd≈ : hd x ≡ hd y
    tl≈ : stream≈ (tl x) (tl y)

open stream≈

stream≈-refl : ∀ {A} {x} -> stream≈ {A} x x
hd≈ (stream≈-refl) = refl
tl≈ (stream≈-refl {x = x}) = stream≈-refl {x = tl x}

stream≈-sym : ∀ {A} {x y} -> stream≈ {A} x y -> stream≈ {A} y x
hd≈ (stream≈-sym s) = sym (hd≈ s)
tl≈ (stream≈-sym s) = stream≈-sym (tl≈ s)

stream≈-trans : ∀ {A} {x y z} -> stream≈ {A} x y -> stream≈ {A} y z -> stream≈ {A} x z
hd≈ (stream≈-trans s t) = λ i -> compPath-filler (hd≈ s) (hd≈ t) i i
tl≈ (stream≈-trans s t) = stream≈-trans (tl≈ s) (tl≈ t)

----------------------------
-- Bisimulation Principle --
----------------------------

stream-bisimulation : ∀ {A} -> bisimulation (stream-S A) M-coalg (stream≈)
αᵣ (stream-bisimulation {A}) (a , b , p) = hd≈ p i0 , (λ x → tl a , tl b , tl≈ p)
rel₁ (stream-bisimulation {A}) i (a , b , p) = (hd a , λ _ → tl a)
rel₂ (stream-bisimulation {A}) i (a , b , p) = (hd≈ p (~ i) , λ _ → tl b)

stream-bisim : ∀ {A} -> ∀ {x y : stream A} -> stream≈ x y -> x ≡ y
stream-bisim {A} {x} {y} = coinduction stream≈ stream-bisimulation

stream-misib : ∀ {A} {x y} -> x ≡ y -> stream≈ {A} x y
stream-misib = coinduction⁻ stream≈ stream-bisimulation stream≈-refl

-- postulate
--   iso1 : {A : Type₀} → {x y : stream A} → (p : x ≡ y) → stream-bisim {A = A} (stream-misib {A = A} p) ≡ p
--   iso2 : {A : Type₀} → {x y : stream A} → (p : stream≈ x y) → stream-misib (stream-bisim p) ≡ p

-- stream≈≡≡ : ∀ {A} -> stream≈ {A} ≡ _≡_
-- stream≈≡≡ = coinduction-is-equality stream≈ stream-bisimulation stream≈-refl
