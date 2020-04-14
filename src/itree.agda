{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Container
open import M
open import Coalg
open import helper

open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Foundations.Embedding

module itree where

delay-helper : ∀ (R : Set) → (Unit ⊎ R) → Set
delay-helper R (inr _) = ⊥
delay-helper R (inl tt) = Unit

-- itrees (and buildup examples)
delay-S : (R : Set₀) -> Container
delay-S R = (Unit ⊎ R) , delay-helper R

delay : (R : Set₀) -> Set₀
delay R = M (delay-S R)

-- ret = now
delay-ret : {R : Set} -> R -> delay R
delay-ret r = in-fun (inr r , λ ())

-- tau = later
delay-tau : {R : Set₀} -> delay R -> delay R
delay-tau t = in-fun (inl tt , λ _ → t)

mutual
  data Delay (R : Set) : Set where
    now : R → Delay R
    later : ∞Delay R → Delay R

  record ∞Delay (R : Set) : Set where
    coinductive
    field
      force : Delay R

open ∞Delay

∞delay-to-∞Delay : ∀ {R} → P₀ {S = delay-S R} (delay R) → ∞Delay R
force (∞delay-to-∞Delay (inr r , b)) = now r
force (∞delay-to-∞Delay (inl tt , t)) = later (∞delay-to-∞Delay (out-fun (t tt)))

delay-to-Delay : ∀ {R} → delay R → Delay R
delay-to-Delay x = force (∞delay-to-∞Delay (out-fun x))

Delay-to-delay-x : ∀ {R} (n : ℕ) → Delay R → X (sequence (delay-S R)) n
Delay-to-delay-x 0 _ = lift tt
Delay-to-delay-x (suc n) (now r) = inr r , λ ()
Delay-to-delay-x (suc n) (later t) = inl tt , λ {tt → Delay-to-delay-x n (force t)}

Delay-to-delay-π : {R : Set} (n : ℕ) (a : Delay R) →  π (sequence (delay-S R)) (Delay-to-delay-x (suc n) a) ≡ Delay-to-delay-x n a
Delay-to-delay-π 0 _ = refl {x = lift tt}
fst (Delay-to-delay-π {R} (suc n) (now r) i) = inr r
snd (Delay-to-delay-π {R} (suc n) (now r) i) ()
Delay-to-delay-π {R} (suc n) (later t) i = (inl tt , λ {tt → Delay-to-delay-π n (force t) i})

Delay-to-delay : ∀ {R} → Delay R → delay R
Delay-to-delay x = lift-to-M Delay-to-delay-x Delay-to-delay-π x

postulate
  delay-equality-section : ∀ {R} (b : Delay R) → delay-to-Delay (Delay-to-delay b) ≡ b
-- delay-equality-section {R} (now r) = refl
-- delay-equality-section {R} (later t) = {!!} -- todo

postulate
  delay-equality-retraction : ∀ {R} (b : delay R) → Delay-to-delay (delay-to-Delay b) ≡ b
-- delay-equality-retraction = {!!}

delay-equality : ∀ {R : Set} -> delay R ≡ Delay R
delay-equality = isoToPath (iso delay-to-Delay Delay-to-delay delay-equality-section delay-equality-retraction)

-- Bottom element raised
data ⊥₁ : Set₁ where

-- TREES
tree-S : (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ-suc ℓ-zero}
tree-S E R = (R ⊎ Σ Set (λ A -> E A)) , (λ { (inl _) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

tree : (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
tree E R = M (tree-S E R)

tree-ret : ∀ {E} {R}  -> R -> tree E R
tree-ret {E} {R} r = in-fun (inl r , λ ())

tree-vis : ∀ {E} {R}  -> ∀ {A} -> E A -> (A -> tree E R) -> tree E R
tree-vis {A = A} e k = in-fun (inr (A , e) , λ { (lift x) -> k x } )

-- ITREES

itree-S : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ-suc ℓ-zero}
itree-S E R = ((Unit ⊎ R) ⊎ Σ Set E) , (λ { (inl (inl _)) -> Lift Unit ; (inl (inr _)) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

itree :  ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
itree E R = M (itree-S E R)

ret' : ∀ {E} {R}  -> R -> P₀ {S = itree-S E R} (itree E R)
ret' {E} {R} r = inl (inr r) , λ ()

tau' : {E : Set₀ -> Set₁} -> {R : Set₀} -> itree E R -> P₀ {S = itree-S E R} (itree E R)
tau' t = inl (inl tt) , λ x → t

vis' : ∀ {E} {R}  -> ∀ {A : Set} -> E A -> (A -> itree E R) -> P₀ {S = itree-S E R} (itree E R)
vis' {A = A} e k = inr (A , e) , λ { (lift x) -> k x }

ret : ∀ {E} {R}  -> R -> itree E R
ret = in-fun ∘ ret'

tau : {E : Set₀ -> Set₁} -> {R : Set₀} -> itree E R -> itree E R
tau = in-fun ∘ tau'

vis : ∀ {E} {R}  -> ∀ {A : Set} -> E A -> (A -> itree E R) -> itree E R
vis {A = A} e = in-fun ∘ (vis' {A = A} e)

-- Bind operations
{-# TERMINATING #-}
bind-helper : ∀ {E : Set -> Set₁} {R S : Set} -> (R -> itree E S) -> P₀ {S = itree-S E R} (itree E R) -> itree E S
bind-helper k (inl (inl tt), b) = tau (bind-helper k (out-fun (b (lift tt))))
bind-helper k (inl (inr r), _) = k r
bind-helper k (inr (A , e), k') = vis e λ (x : A) → bind-helper k (out-fun (k' (lift x)))

bind : ∀ {E} {R} {S} -> itree E R -> (R -> itree E S) -> itree E S
bind {E} {R} {S} t k = bind-helper k (out-fun {S = itree-S E R} t)

syntax bind e₁ (λ x → e₂) = x ← e₁ , e₂

trigger : ∀ {E R} -> E R -> itree E R
trigger e = vis e λ x → ret x
