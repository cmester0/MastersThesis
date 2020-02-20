{-# OPTIONS --cubical --guardedness #-} --safe
module bisim-examples where

open import itree
open import itree2
open import M
open import itree-examples

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open bisimulation

data itree≈ {E} {R} : itree E R -> itree E R -> Set₁ where
  EqRet : ∀ r s -> r ≡ s -> itree≈ (ret r) (ret s)
  EqTau : ∀ t u -> itree≈ t u -> itree≈ (tau t) (tau u)
  EqVis : ∀ {A} e k1 k2 -> k1 ≡ k2 -> itree≈ (vis {A = A} e k1) (vis {A = A} e k2)

open itree≈

-- ((Unit ⊎ R) ⊎ Σ Set E) -,- (λ { (inl (inl _)) -> Lift Unit ; (inl (inr _)) -> ⊥₁ ; (inr (A , e)) -> Lift A } )
itree-bisim : ∀ {E : Set₀ -> Set₁} {R : Set₀} -> bisimulation (itree-S E R) M-coalg
R itree-bisim = itree≈
αᵣ (itree-bisim {E} {R}) = {!!}
rel₁ itree-bisim = λ i → λ a → {!!}
rel₂ itree-bisim = {!!}

spin-it : itree IO ℕ
spin-it = vis Input (λ x -> tau (ret x))

spin-it-eq : spin-it ≡ spin-it
spin-it-eq = coinduction (itree-S IO ℕ) itree-bisim spin-it spin-it (EqVis {!!} {!!} {!!} {!!})

-- -- delay examples
-- data delay≈ {R} : delay R -> delay R -> Set where
--   delay-ret≈ : (r s : R) -> r ≡ s -> delay≈ (delay-ret r) (delay-ret s)
--   delay-tau≈ : (t u : delay R) -> delay≈ t u -> delay≈ (delay-tau t) (delay-tau u)

-- open delay≈

-- delay-bisim : ∀ {R} -> bisimulation (delay-S R) M-coalg
-- R delay-bisim = delay≈
-- αᵣ delay-bisim = {!!}
-- rel₁ delay-bisim = {!!}
-- rel₂ delay-bisim = {!!}

-- ret2≡ret3 : ret2 ≡ ret3
-- ret2≡ret3 = coinduction (delay-S ℕ) delay-bisim ret2 ret3 (delay-tau≈ (delay-ret 2) (delay-ret 2) (delay-ret≈ 2 2 refl))

-- spin≡spin : ∀ {R} -> spin {R} ≡ spin
-- spin≡spin {R = R} = coinduction (delay-S R) delay-bisim spin spin (delay-tau≈ spin spin {!!})
