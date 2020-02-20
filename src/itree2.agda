{-# OPTIONS --cubical --guardedness  #-} --safe

module itree2 where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

-- Delay
record Delay (R : Set₀) : Set₁ where
  coinductive
  field
    ValueD : Delay R ⊎ R

open Delay

DelayIT : Set₀ -> Set₁
DelayIT R = Delay R ⊎ R -- delay inner type

TauD : ∀ {R} -> DelayIT R -> DelayIT R
TauD t = inl record {ValueD = t}

TauD' : ∀ {R} -> Delay R -> DelayIT R
TauD' t = inl t

RetD : ∀ {R} -> R -> DelayIT R
RetD r = inr r

-- Tree
record Tree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueT : Σ Set (λ A -> E A × (A -> Tree E R)) ⊎ R

open Tree

TreeIT : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁ -- tree inner type
TreeIT E R = Σ Set (λ A -> E A × (A -> Tree E R)) ⊎ R

TreeRet : ∀ {E} {R} -> R -> Tree E R
ValueT (TreeRet r) = inr r

TreeVis : ∀ {E} {R} -> ∀ {A} -> E A -> (A -> TreeIT E R) -> TreeIT E R
TreeVis {A = A} e k = inl (A , e , λ x -> record { ValueT = k x } )

-- ITree
record ITree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueIT : ITree E R ⊎ (Σ Set (λ A -> E A × (A -> ITree E R)) ⊎ R)

open ITree

ITree-IT : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
ITree-IT E R = ITree E R ⊎ (Σ Set (λ A -> E A × (A -> ITree E R)) ⊎ R) -- itree inner type

Ret : {E : Set -> Set₁} {R : Set} -> R -> ITree-IT E R
Ret = inr ∘ inr

Tau : {E : Set -> Set₁} {R : Set} -> ITree-IT E R -> ITree-IT E R
Tau t = inl record { ValueIT = t}

Tau' : {E : Set -> Set₁} {R : Set} -> ITree E R -> ITree-IT E R
Tau' t = inl t

Vis : {E : Set -> Set₁} {R : Set} -> ∀ {A} -> E A -> (A -> ITree-IT E R)  -> ITree-IT E R
Vis {A = A} e k = inr (inl (A , e , λ x -> record { ValueIT = k x } ))

Vis' : {E : Set -> Set₁} {R : Set} -> ∀ {A} -> E A -> (A -> ITree E R)  -> ITree-IT E R
Vis' {A = A} e k = inr (inl (A , e , k ))

{-# NON_TERMINATING #-}
Bind : ∀ {E R S} -> ITree-IT E R -> (R -> ITree-IT E S) -> ITree-IT E S
Bind (inr (inr r)) k = k r
Bind (inl t) k = Tau (Bind (ValueIT t) k)
Bind (inr (inl (A , e , k))) k' = Vis e λ x → Bind (ValueIT (k x)) k'

-- {-# NON_TERMINATING #-}
-- Bind : ∀ {E R S} -> ITree E R -> (R -> ITree E S) -> ITree-IT E S
-- Bind S k = case ValueIT S of λ { (inr (inr r)) → ValueIT (k r)
--                                  ; (inl t) -> inl (record { ValueIT = Bind t k })
--                                  ; (inr (inl (A , e , k'))) -> inr (inl ( A , e , λ x → record { ValueIT = Bind (k' x) k } ))} -- Tau' (Bind t k)

Trigger : ∀ {E} {R} -> (e : E R) -> ITree-IT E R
Trigger e = Vis e Ret

Trigger' : ∀ {E} {R} -> (e : E R) -> ITree E R
ValueIT (Trigger' e) = Vis e Ret
