{-# OPTIONS --cubical --guardedness #-} --safe
module helper where

open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to empty-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥rec∥ ; elim to ∥elim∥ ; map to ∥map∥)

------------------------
-- Helper definitions --
------------------------

double-prop-to-single : ∀ {ℓ : Level} {A : Type ℓ} → Iso (∥ ∥ A ∥ ∥) (∥ A ∥)
Iso.fun (double-prop-to-single {A = A}) = ∥rec∥ propTruncIsProp (idfun ∥ A ∥)
Iso.inv double-prop-to-single = ∣_∣
Iso.rightInv double-prop-to-single _ = refl
Iso.leftInv double-prop-to-single = ∥elim∥ (λ _ → isProp→isSet propTruncIsProp _ _) (λ _ → refl)

Axiom-of-countable-choice : (ℓ : Level) → Set (ℓ-suc ℓ)
Axiom-of-countable-choice ℓ = {B : ℕ → Set ℓ} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

isInjective : ∀ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type _
isInjective f = ∀{w x} → f w ≡ f x → w ≡ x

inl≢inr : ∀ {A : Set} {B : Set} → {x : A} {y : B} → inl x ≡ inr y → ⊥
inl≢inr {A = A} {B} x = subst (λ {(inl x) → A ⊎ B ; (inr y) → ⊥}) x (x i0)

isEmbedding→Injection-x :
  ∀ {ℓ} {A B : Type ℓ}
  → (a : A -> B)
  → (e : isEmbedding a) →
  ----------------------
  ∀ x y → (a x ≡ a y) ≡ (x ≡ y)
isEmbedding→Injection-x a e x y = sym (ua (cong a , e x y))

-- Quotient recursor
rec :
  ∀ {ℓ} {A B : Type ℓ} {R : A → A → Type ℓ}
  → (f : A → B)
  → (∀ x y → R x y → f x ≡ f y)
  → isSet B
  → A / R → B
rec {A = A} {B} {R} f feq B-set x = rec' x
 where
   rec' : A / R → B
   rec' [ x ] = f x
   rec' (eq/ a b r i) = feq a b r i
   rec' (squash/ a b p q i j) = B-set (rec' a) (rec' b) (cong rec' p) (cong rec' q) i j
