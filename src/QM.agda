{-# OPTIONS --cubical --guardedness #-} --safe

open import itree
open import M
open import Coalg

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma hiding (_×_)
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
open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Binary

open import Cubical.HITs.SetQuotients

open import Container
open import helper

open import Cubical.Data.Nat.Order
open import M

module QM where

compat : ∀ {ℓ} {X Y : Set ℓ} {R : X → X → Set ℓ} (f : X → Y) → Set ℓ
compat {X = X} {R = R} f = {x₁ x₂ : X} → R x₁ x₂ → f x₁ ≡ f x₂


record QM {ℓ} (S : Container {ℓ}) (R : M S → M S → Set ℓ) : Set (ℓ-suc ℓ) where
  field
    QM-ty : Set ℓ
    []M : M S → QM-ty
    sound : ∀ {x y : M S} → R x y → []M x ≡ []M y
    
  dcompat : (Y : QM-ty → Set ℓ) (f : (x : M S) → (Y ([]M x))) → Set ℓ
  dcompat Y f = ∀ {x y : M S} → (r : R x y) → subst Y (sound r) (f x) ≡ f y

  field
    lift' : ∀ (Y : QM-ty → Set ℓ) (f : (x : M S) → (Y ([]M x))) → (p : dcompat Y f) → (q : QM-ty) → Y q
    liftβ : ∀ (Y : QM-ty → Set ℓ) (f : (x : M S) → (Y ([]M x))) → (p : dcompat Y f) (x : M S) → lift' Y f p ([]M x) ≡ f x

open QM

mutual
  data _∼_ {R} : (x y : delay R) → Set where
    ∼now   : ∀ {r} → delay-ret r ∼ delay-ret r
    ∼later : ∀ {x y} → x ∞∼ y → (delay-tau x) ∼ (delay-tau y)

  record _∞∼_ {R} (x y : delay R) : Set where
    coinductive
    field
      force : x ∼ y

data _↓_ {R} : delay R → R → Set where
  ↓now : ∀ r b → in-fun (inr r , b) ↓ r
  ↓later : ∀ t r → (t tt) ↓ r → in-fun (inl tt , t) ↓ r

postulate
  terminate : (∀ {R} (x : delay R) (a a' : R) → x ↓ a → x ↓ a' → a ≡ a')

shift : ∀ {R} → delay R → delay R ⊎ R
shift {R = R} p = case out-fun p return (λ x → delay R ⊎ R) of λ {(inr r , b) → inr r ; (inl tt , t) → inl (t tt)}

unshift : ∀ {R} → delay R ⊎ R → delay R
unshift (inl r) = delay-tau r
unshift (inr r) = delay-ret r

repeat-n-shift : ∀ {R} → delay R → ℕ → delay R ⊎ R
repeat-n-shift r 0 = inl r
repeat-n-shift r (suc n) = case (shift r) of λ {(inl r) → repeat-n-shift r n ; (inr r) → inr r}

is-never : ∀ {R} → delay R → R ⊎ Unit
is-never = {!!}

is-mon : ∀ {R} → (g : ℕ → R ⊎ Unit) → Set
is-mon g = (n : ℕ) → (g n ≡ g (suc n)) ⊎ ((g n ≡ inr tt) × (g (suc n) ≡ inr tt → ⊥))

seq : ∀ {R : Set} → Set
seq {R} = Σ (ℕ → R ⊎ Unit) λ g → is-mon g

_≈_ : ∀ {R} → delay R → delay R → Set
_≈_ {R = R} x y = (a : R) → (x ↓ a → y ↓ a) × (y ↓ a → x ↓ a)

asdf : ∀ R → QM (delay-S R) _≈_
QM-ty (asdf R) = R ⊎ Unit
[]M (asdf R) x = {!!}
sound  (asdf R) {x = x} {y} p = {!!}


