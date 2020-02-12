{-# OPTIONS --cubical --guardedness --copatterns #-}  --safe 

module itree2 where

  open import Cubical.Foundations.Everything
  open import Cubical.Core.Everything

  open import Cubical.Data.Nat as ℕ using (ℕ)
  open import Cubical.Data.Empty
  open import Cubical.Data.Unit
  open import Cubical.Data.Bool
  open import Cubical.Data.Prod
  open import Cubical.Data.Sum

  open import Cubical.Codata.M

  open import Later

  data itree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
    Ret : R -> itree E R
    Tau : ▹ (itree E R) -> itree E R
    Vis : ∀ {A} -> E A -> (A -> ▹ itree E R) -> itree E R

  -- itree operations
  trigger : ∀ {E : Set₀ -> Set₁} {A : Set₀} -> E A ->  itree E A
  trigger e = Vis e (next ∘ Ret)

  -- Monadic operations
  bind-pre : ∀ {E R S} -> ▹ (itree E R -> (R -> itree E S) -> itree E S) -> itree E R -> (R -> itree E S) -> itree E S
  bind-pre bind (Ret r) k = k r
  bind-pre bind (Tau t) k = Tau ((bind ⊛ t) ⊛ next k)
  bind-pre bind (Vis {A = A} e f) k = Vis e (λ (x : A) → (bind ⊛ (f x)) ⊛ next k)

  bind : ∀ {E R S} -> itree E R -> (R -> itree E S) -> itree E S
  bind = fix bind-pre

  -- Examples
  data IO : Type₀ → Type₁ where
    Input : IO ℕ
    Output : (x : ℕ) -> IO Unit

  -- Spin definition
  spin-pre : ▹ itree IO ⊥ -> itree IO ⊥
  spin-pre spin = Tau spin

  spin : itree IO ⊥
  spin = fix spin-pre

  spin-unroll : spin ≡ spin-pre (next spin)
  spin-unroll = fix-eq spin-pre

  -- Echo definition
  echo-pre : ▹ itree IO ⊥ -> itree IO ⊥
  echo-pre echo = fix λ y -> (Vis Input λ x -> next (Vis (Output x) λ _ → next (Tau echo)))

  echo : itree IO ⊥
  echo = fix echo-pre

  echo-unroll : echo ≡ echo-pre (next echo)
  echo-unroll = fix-eq echo-pre

  postulate
    later-path : ∀ {ℓ} {A : Set ℓ} {x y : A} -> Path (Set ℓ) (▹ (Path A x y)) (Path (▹ A) (next x) (next y))
    tau-eq : ∀ {E} {R} {x : itree E R} -> Path (itree E R) (Tau (next x)) x

