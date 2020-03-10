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

module itree where

-- itrees (and buildup examples)
delay-S : (R : Set₀) -> Container
delay-S R = (Unit ⊎ R) , λ { (inr _) -> ⊥ ; (inl tt) -> Unit }

delay : (R : Set₀) -> Set₀
delay R = M (delay-S R)

delay-ret : {R : Set} -> R -> delay R
delay-ret r = in-fun (inr r , λ ())

delay-tau : {R : Set₀} -> delay R -> delay R
delay-tau S = in-fun (inl tt , λ x → S)

-- remove-tau : ∀ {R} -> delay R -> delay R
-- remove-tau {R} x = case out-fun x return (λ x₁ → delay R) of λ { (inr r , b) → x ; (inl tt , b) -> b tt }

repeat : ∀ {ℓ} {A : Set ℓ} (x : A -> A) (n : ℕ) -> A -> A
repeat x 0 a = a
repeat x (suc n) a = repeat x n (x a)

open Chain

-- lliifftt : ∀ {ℓ} -> (S : Container {ℓ}) -> (n : ℕ) -> (W (Ms S) (suc n) -> W (Ms S) (suc n)) -> W (Ms S) n -> W (Ms S) n
-- lliifftt S n f x = πₙ S (f ? .fst )

-- MW : ∀ {ℓ} -> (S : Container {ℓ}) -> (n : ℕ) -> (f : W S n -> W S n) -> Set ℓ
-- MW {ℓ = ℓ} S 0 f = Lift {ℓ-zero} {ℓ} Unit -> Lift {ℓ-zero} {ℓ} Unit
-- MW S (suc n) f = {!!}

-- Mπₙ : ∀ {ℓ} -> (S : Container {ℓ}) -> {n : ℕ} (f : W S n -> W S n) -> MW S (suc n) f -> MW S n
-- Mπₙ {ℓ} S {0} = λ _ _ → lift tt
-- Mπₙ S {suc n} = P₁ (Mπₙ S {n})

-- Msequence : ∀ {ℓ} -> Container {ℓ} -> Chain {ℓ}
-- X (Msequence {ℓ} S) n = MW {ℓ} S n
-- π (Msequence {ℓ} S) {n} = Mπₙ {ℓ} S {n}

-- MM : ∀ {ℓ} -> Container {ℓ} → Set ℓ
-- MM = L ∘ Msequence

-- as : ∀ {R} -> MM (delay-S R)
-- as = {!!}

-- W : ∀ {ℓ} -> Container {ℓ} -> ℕ -> Set ℓ -- (ℓ-max ℓ ℓ')
-- W S 0 = Lift Unit
-- W S (suc n) = P₀ {S = S} (W S n)

-- πₙ : ∀ {ℓ} -> (S : Container {ℓ}) -> {n : ℕ} -> W S (suc n) -> W S n
-- πₙ {ℓ} S {0} = ! {ℓ}
-- πₙ S {suc n} = P₁ (πₙ S {n})

-- sequence : ∀ {ℓ} -> Container {ℓ} -> Chain {ℓ}
-- X (sequence {ℓ} S) n = W {ℓ} S n
-- π (sequence {ℓ} S) {n} = πₙ {ℓ} S {n}

-- M : ∀ {ℓ} -> Container {ℓ} → Set ℓ
-- M = L ∘ sequence

-- repeat-chain : ∀ {A : Set} -> M-Chain {ℓ = ℓ-zero} (delay-S A)
-- MX (repeat-chain) 0 x = lift tt
-- MX (repeat-chain) (suc n) x = inl tt , λ x₁ → (λ { (inr _) → ⊥ ; (inl tt) → Unit }) (fst x)
-- Mπ (repeat-chain) {0} f x = π (f (x))

-- fixpoint = λ {R} (f : delay R -> delay R) -> L ((λ x → {!!}) ,, {!!})

-- L : ∀ {ℓ} -> Chain {ℓ} → Set ℓ
-- L (x ,, pi) = Σ ((n : ℕ) → x n) λ x → (n : ℕ) → pi {n = n} (x (suc n)) ≡ x n

-- fixpoint : ∀ {R} -> (f : (delay R -> delay R) -> delay R -> delay R) -> (x : delay R) -> delay R
-- fixpoint f x = f (fixpoint f) x

-- spin = fixpoint delay-tau

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
