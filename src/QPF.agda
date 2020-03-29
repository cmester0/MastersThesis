{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe
module QPF where

open import M
open import Coalg
open import Cubical.HITs.SetQuotients
open import itree

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )

open Chain

-----------------------
-- Quotiented M-type --
-----------------------

QM : ∀ {ℓ} {S : Container {ℓ}} (R : M S -> M S -> Set) -> Set ℓ
QM {S = S} R = M S / R

record qpf {ℓ} {S : Container {ℓ}} (F₀ : {S : Container {ℓ}} -> Set ℓ -> Set ℓ) (F₁ : {S : Container {ℓ}} -> ∀ {X Y} (f : X -> Y) -> F₀ {S = S} X -> F₀ {S = S} Y) : Set (ℓ-suc ℓ) where
  field
    abs : ∀ {α : Set ℓ} -> P₀ {S = Ms S} α -> F₀ {S = Ms S} α
    repr : ∀ {α : Set ℓ} -> F₀ α -> P₀ {S = Ms S} α
    abs_repr : ∀ {α : Set ℓ} (x : F₀ {S = Ms S} α) -> abs {α} ∘ repr ≡ (λ x -> x)
    abs_map : ∀ {α β : Set ℓ} (f : α -> β) -> abs ∘ (P₁ f) ≡ (F₁ f) ∘ abs

  sequenceF-pre₀ : Container {ℓ} -> ℕ -> Set ℓ -- (ℓ-max ℓ ℓ')
  sequenceF-pre₀ S 0 = Lift Unit
  sequenceF-pre₀ S (suc n) = F₀ {S = S} (sequenceF-pre₀ S n)

  sequenceF-pre₁ : (S : Container {ℓ}) -> {n : ℕ} -> sequenceF-pre₀ S (suc n) -> sequenceF-pre₀ S n
  sequenceF-pre₁ S {0} = ! {ℓ}
  sequenceF-pre₁ S {suc n} = F₁ (sequenceF-pre₁ S {n})

  sequenceF : Container {ℓ} -> Chain {ℓ}
  X (sequenceF S) n = sequenceF-pre₀ S n
  π (sequenceF S) {n} = sequenceF-pre₁ S {n}

  QpfM : Set ℓ
  QpfM = (L ∘ sequenceF) (Ms S)

  QMs : Container
  QMs = QpfM , λ x → F₀ {S = Ms S} QpfM

open qpf
