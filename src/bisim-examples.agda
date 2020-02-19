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

ret2≡ret3 : ret2 ≡ ret3
ret2≡ret3 = coinduction (delay-S ℕ) delay-bisim ret2 ret3 (delay-tau≈ (delay-ret 2) (delay-ret 2) (delay-ret≈ 2 2 refl))

spin≡spin : ∀ {R} -> spin {R} ≡ spin
spin≡spin {R = R} = coinduction (delay-S R) delay-bisim spin spin (delay-tau≈ spin spin {!!})
