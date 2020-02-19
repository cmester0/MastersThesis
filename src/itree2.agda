{-# OPTIONS --cubical --guardedness  #-} --safe

module itree2 where

open import Cubical.Codata.M

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

-- delay-S : (R : Set₀) -> {!!}
-- delay-S R = (Unit ⊎ R) , λ { (inr _) -> ⊥ ; (inl tt) -> Unit }

delay : (R : Set₀) -> Set₀
delay R = M ((λ x → Unit ⊎ R) , λ { _ (inr _) _ → ⊥ ; _ (inl tt) _ -> Unit } ) tt

delay-ret : {R : Set₀} -> R -> delay R
delay-ret r = in

-- delay-ret : {R : Set₀} -> R -> delay R
-- delay-ret r = {!!} (inr r , λ ())

-- delay-tau : {R : Set₀} -> delay R -> delay R
-- delay-tau S = {!!} (inl tt , λ x → S)
