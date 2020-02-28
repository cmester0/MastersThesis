{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe
module QPF where

open import M
open import Coalg
open import Cubical.HITs.SetQuotients

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )

open Chain

QM : ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set) -> Set ℓ
QM S R = M S / R

delay-S : (R : Set₀) -> Container
delay-S R = (Unit ⊎ R) , λ { (inr _) -> ⊥ ; (inl tt) -> Unit }

delay : (R : Set₀) -> Set₀
delay R = M (delay-S R)

delay-ret : {R : Set₀} -> R -> delay R
delay-ret r = in-fun (inr r , λ ())

delay-tau : {R : Set₀} -> delay R -> delay R
delay-tau S = in-fun (inl tt , λ x → S)

data delay≈ {R} : (delay R) -> (delay R) -> Set where
  EqPNow : ∀ r s -> r ≡ s -> delay≈ (delay-ret r) (delay-ret s)
  EqPLater : ∀ t u -> delay≈ t u -> delay≈ (delay-tau t) (delay-tau u)

data weak-delay≈ {R} : (delay R) -> (delay R) -> Set where
  EqNow : ∀ {r s} -> r ≡ s -> weak-delay≈ (delay-ret r) (delay-ret s)
  EqLater : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) (delay-tau u)
  EqLaterL : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) u
  EqLaterR : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ t (delay-tau u)

QDelay : ∀ {R} -> delay R -> QM (delay-S R) weak-delay≈
QDelay = [_]

weak-equivalence-delay-ex0 : QDelay (delay-tau (delay-ret 2)) ≡ QDelay (delay-ret 2)
weak-equivalence-delay-ex0 = eq/ (delay-tau (delay-ret 2)) (delay-ret 2) (EqLaterL (EqNow refl))

-- record qpf {ℓ} {S : Container {ℓ}} (F₀ : {S : Container {ℓ}} -> Set ℓ -> Set ℓ) (F₁ : {S : Container {ℓ}} -> ∀ {X Y} (f : X -> Y) -> F₀ {S = S} X -> F₀ {S = S} Y) : Set (ℓ-suc ℓ) where
--   field
--     abs : ∀ {α : Set ℓ} -> P₀ {S = Ms S} α -> F₀ {S = Ms S} α
--     repr : ∀ {α : Set ℓ} -> F₀ α -> P₀ {S = Ms S} α
--     abs_repr : ∀ {α : Set ℓ} (x : F₀ {S = Ms S} α) -> abs {α} ∘ repr ≡ (λ x -> x)
--     abs_map : ∀ {α β : Set ℓ} (f : α -> β) -> abs ∘ (P₁ f) ≡ (F₁ f) ∘ abs

--   sequenceF-pre₀ : Container {ℓ} -> ℕ -> Set ℓ -- (ℓ-max ℓ ℓ')
--   sequenceF-pre₀ S 0 = Lift Unit
--   sequenceF-pre₀ S (suc n) = F₀ {S = S} (sequenceF-pre₀ S n)

--   sequenceF-pre₁ : (S : Container {ℓ}) -> {n : ℕ} -> sequenceF-pre₀ S (suc n) -> sequenceF-pre₀ S n
--   sequenceF-pre₁ S {0} = ! {ℓ}
--   sequenceF-pre₁ S {suc n} = F₁ (sequenceF-pre₁ S {n})

--   sequenceF : Container {ℓ} -> Chain {ℓ}
--   X (sequenceF S) n = sequenceF-pre₀ S n
--   π (sequenceF S) {n} = sequenceF-pre₁ S {n}

--   QM : Set ℓ
--   QM = (L ∘ sequenceF) (Ms S)
  
--   QMs : Container
--   QMs = QM , λ x → F₀ {S = Ms S} QM

-- open qpf
