{-# OPTIONS --cubical --guardedness #-} --safe

open import M
open import Coalg

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Embedding
open import Agda.Builtin.Cubical.Glue

module itree-extended where

-- itrees (and buildup examples)
delay-S : (R : Set₀) -> Container
delay-S R = (Unit ⊎ R) , λ { (inr _) -> ⊥ ; (inl tt) -> Unit }

delay : (R : Set₀) -> Set₀
delay R = M (delay-S R)

delay-ret : {R : Set₀} -> R -> delay R
delay-ret r = in-fun (inr r , λ ())

delay-tau : {R : Set₀} -> delay R -> delay R
delay-tau S = in-fun (inl tt , λ x → S)

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

data itree-T (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  retT : R -> itree-T E R
  tauT : itree-T E R
  visT : ∀ {A} -> E A -> itree-T E R

itree-S : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ-suc ℓ-zero}
itree-S E R = itree-T E R , λ { tauT -> Lift Unit ; (retT _) -> ⊥₁ ; (visT {A} _) -> Lift A }

itree :  ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
itree E R = M (itree-S E R)

ret' : ∀ {E} {R}  -> R -> P₀ {S = itree-S E R} (itree E R)
ret' {E} {R} r = retT r , λ ()

tau' : {E : Set₀ -> Set₁} -> {R : Set₀} -> itree E R -> P₀ {S = itree-S E R} (itree E R)
tau' t = tauT , λ x → t

vis' : ∀ {E} {R}  -> ∀ {A : Set} -> E A -> (A -> itree E R) -> P₀ {S = itree-S E R} (itree E R)
vis' {A = A} e k = visT e , λ { (lift x) -> k x } 

ret : ∀ {E} {R}  -> R -> itree E R
ret = in-fun ∘ ret'

tau : {E : Set₀ -> Set₁} -> {R : Set₀} -> itree E R -> itree E R
tau = in-fun ∘ tau'

vis : ∀ {E} {R}  -> ∀ {A : Set} -> E A -> (A -> itree E R) -> itree E R
vis {A = A} e = in-fun ∘ (vis' {A = A} e)

help : ∀ {R : Set} -> isProp R -> isSet R
help = isProp→isSet

-- TODO:
-- r-set-tree-set : ∀ {E} {R : Set} -> isSet R -> isSet (itree E R)
-- r-set-tree-set = {!!}

-- asdff : ∀ E R (k : Set) -> (itree-T E R -> k) -> itree E R -> k
-- asdff E R f = {!!}

-- isEmbedding?
-- injSuc : ∀ {E} {R} {r s : R} -> ret {E = E} r ≡ ret s → r ≡ s
-- injSuc {E} {R} p = (λ (f : itree E R → R) -> cong f p) (asdff E R R λ { (retT r) → r ; tauT -> {!!} ; (visT e) -> {!!} } )

-- Σ ((n : ℕ) → sequence-pre₀ (itree-S E R) n)
--     (λ x → (n : ℕ) → sequence-pre₁ (itree-S E R) (x (suc n)) ≡ x n)

-- Bind operations
{-# TERMINATING #-}
bind-helper : ∀ {E : Set -> Set₁} {R S : Set} -> (R -> itree E S) -> P₀ {S = itree-S E R} (itree E R) -> itree E S
bind-helper k (tauT , b) = tau (bind-helper k (out-fun (b (lift tt))))
bind-helper k ((retT r) , _) = k r
bind-helper k ((visT {A} e), k') = vis e λ (x : A) → bind-helper k (out-fun (k' (lift x)))

bind : ∀ {E} {R} {S} -> itree E R -> (R -> itree E S) -> itree E S
bind {E} {R} {S} t k = bind-helper k (out-fun {S = itree-S E R} t)

trigger : ∀ {E R} -> E R -> itree E R
trigger e = vis e λ x → ret x
