{-# OPTIONS --cubical --guardedness  #-} --safe

module itree where

open import M

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

-- Data types used in examples
data IO : Type₀ → Type₁ where
  Input : IO ℕ
  Output : (x : ℕ) -> IO Unit

-- itrees (and buildup examples)
record Delay (R) : Set₀ where
  coinductive
  field
    ValueD : Delay R ⊎ R

open Delay

RetD : {R : Set₀} -> R -> Delay R
ValueD (RetD r) = inr r

TauD : {R : Set₀} -> Delay R -> Delay R
ValueD (TauD t) = inl t

delay-S : (R : Set₀) -> Container
delay-S R = (Unit ⊎ R) -,- λ { (inr _) -> ⊥ ; (inl tt) -> Unit }

delay : (R : Set₀) -> Set₀
delay R = M (delay-S R)

delay-ret : {R : Set₀} -> R -> delay R
delay-ret r = in-fun (inr r , λ ())

delay-tau : {R : Set₀} -> delay R -> delay R
delay-tau S = in-fun (inl tt , λ x → S)

-- delay examples
spin : ∀ {R} -> Delay R
ValueD spin = inl spin

{-# NON_TERMINATING #-}
spin2 : ∀ {R} -> delay R
spin2 {R} = delay-tau {R = R} spin2

delay-once : ∀ {R} -> R -> Delay R
delay-once r = TauD (RetD r)

delay-twice : ∀ {R} -> R -> Delay R
delay-twice r = TauD (TauD (TauD (TauD (RetD r))))

-- TREES

record Tree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueT : Σ Set (λ A -> E A × (A -> Tree E R)) ⊎ R

open Tree

TreeRet : ∀ {E} {R} -> R -> Tree E R
ValueT (TreeRet r) = inr r

TreeVis : ∀ {E} {R} -> ∀ {A} -> E A -> (A -> Tree E R) -> Tree E R
ValueT (TreeVis {A = A} e k) = inl (A , e , k)

tree-S : (E : Set₀ -> Set₁) (R : Set₀) -> Container 
tree-S E R = (R ⊎ Σ Set (λ A -> E A)) -,- (λ { (inl _) -> ⊥ ; (inr (A , e)) -> Lift A } )

tree : (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
tree E R = M (tree-S E R)

tree-ret : ∀ {E} {R}  -> R -> tree E R
tree-ret {E} {R} r = in-fun (inl r , λ ())

tree-vis : ∀ {E} {R}  -> ∀ {A} -> E A × (A -> tree E R) -> tree E R
tree-vis {E} {R} {A} (e , k) = in-fun (inr (A , e) , λ { (lift x) → k x })

-- ITREES
record ITree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueIT : ITree E R ⊎ (Σ Set (λ A -> E A × (A -> ITree E R)) ⊎ R)

-- itree : ∀ {E : Set₀ -> Set₁} {R : Set₀} -> Set₁
-- itree {E} {R} = M (Unit -,- λ { tt -> ? ⊎ (Σ Set (λ A -> E A × (A -> ?)) ⊎ R) } )

open ITree

Ret : {E : Set -> Set₁} {R : Set} -> R -> ITree E R
ValueIT (Ret r) = inr (inr r)

Tau : {E : Set -> Set₁} {R : Set} -> ITree E R -> ITree E R
ValueIT (Tau t) = inl t

Vis : {E : Set -> Set₁} {R : Set} {A : Set} -> E A -> (A -> ITree E R) -> ITree E R
ValueIT (Vis {A = A} e k) = inr (inl (A , e , k))

{-# NON_TERMINATING #-}
echo : ITree IO Unit
echo = Vis Input λ x → Vis (Output x) λ x₁ → Tau echo
