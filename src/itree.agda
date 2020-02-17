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
delay-S R = (Unit -,- λ { _ -> Unit ⊎ R })

delay : (R : Set₀) -> Set₀
delay R = M (delay-S R)

delay-ret-pre : {R : Set₀} -> (R -> delay R) -> R -> delay R
delay-ret-pre S r = out-fun (S r) .snd (inr r)

{-# NON_TERMINATING #-}
delay-ret : {R : Set₀} -> R -> delay R
delay-ret = delay-ret-pre delay-ret

delay-tau : {R : Set₀} -> delay R -> delay R
delay-tau S = out-fun S .snd (inl tt)

temp : ∀ (y : Σ Set₀ λ A -> A -> Unit) (x : y .fst -> Unit) -> x ≡ y .snd
temp y x = refl

-- delay examples
spin : ∀ {R} -> Delay R
ValueD spin = inl spin

delay-once : ∀ {R} -> R -> Delay R
delay-once r = TauD (RetD r)

delay-twice : ∀ {R} -> R -> Delay R
delay-twice r = TauD (TauD (TauD (TauD (RetD r))))

-- Binary trees
record BinTree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueBT : (E Bool × (Bool -> BinTree E R)) ⊎ R

open BinTree

BinTreeRet : ∀ {E} {R} -> R -> BinTree E R
ValueBT (BinTreeRet r) = inr r

BinTreeVis : ∀ {E} {R} -> E Bool -> (Bool -> BinTree E R) -> BinTree E R
ValueBT (BinTreeVis e k) = inl (e , k)

{-# NON_TERMINATING #-}
bintree2-S : (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ = ℓ-suc ℓ-zero}
bintree2-S E R = (Lift R -,- λ _ -> E Bool × (Bool -> M (bintree2-S E R)))

tree2 : (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
tree2 E R = M (bintree2-S E R)

tree-ret : ∀ {E} {R}  -> tree2 E R -> R -> tree2 E R 
tree-ret {E} {R} t r = out-fun t .snd {!!}

bintree-vis : ∀ {E} {R}  -> Σ Set (λ A -> E A × (A -> BinTree E R)) -> tree2 E R
bintree-vis {E} {R} r = in-fun {S = bintree2-S E R} ({!!} , {!!})

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

{-# NON_TERMINATING #-}
tree-S : (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ = ℓ-suc ℓ-zero}
tree-S E R = (Lift R -,- λ _ -> Σ Set (λ A -> E A × (A -> M (tree-S E R))))

tree-S-S : (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ = ℓ-suc ℓ-zero}
tree-S-S E R = (Lift ⊥ -,- λ _ -> R ⊎ (Σ Set (λ A -> E A × (A -> M (tree-S E R)))))

tree : (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
tree E R = M (tree-S-S E R)


-- tree-ret : ∀ {E} {R}  -> Σ Set (λ A -> E A × (A -> Tree E R)) ⊎ R -> tree E R
-- tree-ret {E} {R} r = in-fun {S = tree-S-S E R} {!!}

-- cons : ∀ {A} -> A -> stream A -> stream A
-- cons x xs = in-fun (x , λ { tt -> xs } )

test : Tree IO ℕ
test = TreeRet ℕ.zero

-- testt : tree IO ℕ
-- testt = tree-ret ℕ.zero

-- tree-vis : ∀ {E} {R} -> ∀ {A} -> E A -> (A -> tree E R) -> tree E R
-- tree-vis {A = A} e k = out-fun {!!} .snd (A , e , {!!})

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
