{-# OPTIONS --cubical --guardedness  #-} --safe

module itree-examples where

open import itree
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

-- Delay examples
record Delay (R : Set₀) : Set₁ where
  coinductive
  field
    ValueT : Delay R ⊎ R

open Delay

DelayIT : Set₀ -> Set₁
DelayIT R = Delay R ⊎ R -- delay inner type

TauD : ∀ {R} -> Delay R -> Delay R
ValueT (TauD t) = inl t

RetD : ∀ {R} -> R -> Delay R
ValueT (RetD r) = inr r

TauD' : ∀ {R} -> Delay R -> DelayIT R
TauD' t = inl t

RetD' : ∀ {R} -> R -> DelayIT R
RetD' r = inr r

-- delay examples
data delay≈ {R} : delay R -> delay R -> Set where
  delay-ret≈ : (r s : R) -> r ≡ s -> delay≈ (delay-ret r) (delay-ret s)
  delay-tau≈ : (t u : delay R) -> delay≈ t u -> delay≈ (delay-tau t) (delay-tau u)

open delay≈
open bisimulation

delay-bisim : ∀ {R} -> bisimulation (delay-S R) M-coalg
R delay-bisim = delay≈
αᵣ delay-bisim = λ x → inl tt , λ x₁ → ((λ n → {!!}) , (λ n i → {!!})) , (({!!} , (λ n i → {!!})) , {!!})
rel₁ delay-bisim = {!!}
rel₂ delay-bisim = {!!}

ret2 : delay ℕ
ret2 = delay-tau (delay-ret 2)

ret3 : delay ℕ
ret3 = delay-tau (delay-ret 2)

ret2≡ret3 : ret2 ≡ ret3
ret2≡ret3 = coinduction (delay-S ℕ) delay-bisim ret2 ret3 (delay-tau≈ (delay-ret 2) (delay-ret 2) (delay-ret≈ 2 2 refl))

{-# NON_TERMINATING #-}
spins : ∀ {R} -> delay R
spins {R} = delay-tau {R = R} spins

spin2 : ∀ {R} -> delay R
spin2 {R} = delay-tau {R = R} spins

spin3 : ∀ {R} -> delay R
spin3 {R} = delay-tau {R = R} spins

spin2≡spin3 : ∀ {R} -> spin2 {R} ≡ spin3
spin2≡spin3 {R = R} = coinduction (delay-S R) delay-bisim spin2 spin3 (delay-tau≈ spins spins {!!})

delay-once : ∀ {R} -> R -> Delay R
delay-once r = TauD (RetD r)

delay-twice : ∀ {R} -> R -> Delay R
delay-twice r = TauD (TauD (TauD (TauD (RetD r))))

-- Tree examples
record Tree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueT : Σ Set (λ A -> E A × (A -> Tree E R)) ⊎ R

open Tree

TreeRet : ∀ {E} {R} -> R -> Tree E R
ValueT (TreeRet r) = inr r

TreeVis : ∀ {E} {R} -> ∀ {A} -> E A -> (A -> Tree E R) -> Tree E R
ValueT (TreeVis {A = A} e k) = inl (A , e , k)

-- ITree examples
record ITree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueIT : ITree E R ⊎ (Σ Set (λ A -> E A × (A -> ITree E R)) ⊎ R)

open ITree

ITree-IT : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
ITree-IT E R = ITree E R ⊎ (Σ Set (λ A -> E A × (A -> ITree E R)) ⊎ R) -- inner type

Ret : {E : Set -> Set₁} {R : Set} -> R -> ITree E R
ValueIT (Ret r) = inr (inr r)

Tau : {E : Set -> Set₁} {R : Set} -> ITree E R -> ITree E R
ValueIT (Tau t) = inl t

Vis : {E : Set -> Set₁} {R : Set} {A : Set} -> E A -> (A -> ITree E R) -> ITree E R
ValueIT (Vis {A = A} e k) = inr (inl (A , e , k))

Ret' : {E : Set -> Set₁} {R : Set} -> R -> ITree-IT E R
Ret' = inr ∘ inr

Tau' : {E : Set -> Set₁} {R : Set} -> ITree E R -> ITree-IT E R
Tau' = inl

Vis' : {E : Set -> Set₁} {R : Set} -> ∀ {A} -> E A -> (A -> ITree-IT E R)  -> ITree-IT E R
Vis' {A = A} e k = inr (inl (A , e , λ x -> record { ValueIT = k x } ))

Spin : ITree IO Unit
ValueIT Spin = inl Spin

Spin2 : ITree IO Unit
ValueIT Spin2 = Tau' Spin2

Echo : ITree IO Unit
ValueIT Echo = inr (inl (ℕ , (Input , λ x → record { ValueIT = inr (inl (Unit , (Output x , λ x₁ → record { ValueIT = inl Echo }))) })))

Echo2 : ITree IO Unit
ValueIT Echo2 = Vis' (Input) λ x → Vis' (Output x) λ x₁ → Tau' Echo2

{-# NON_TERMINATING #-}
echo : itree IO Unit
echo = vis Input λ x → vis (Output x) λ _ → tau echo
