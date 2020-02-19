{-# OPTIONS --cubical --guardedness  #-} --safe

module itree-examples where

open import itree
open import itree2
open import M

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open Delay
open ITree

-- Data types used in examples
data IO : Type₀ → Type₁ where
  Input : IO ℕ
  Output : (x : ℕ) -> IO Unit


--------------------
-- Delay examples --
--------------------

ret2 : delay ℕ
ret2 = delay-tau (delay-ret 2)

ret3 : delay ℕ
ret3 = delay-tau (delay-ret 2)

{-# NON_TERMINATING #-}
spin : ∀ {R} -> delay R
spin {R} = delay-tau {R = R} spin

delay-once : ∀ {R} -> R -> Delay R
ValueD (delay-once r) = TauD (RetD r)

delay-twice : ∀ {R} -> R -> Delay R
ValueD (delay-twice r) = TauD (TauD (TauD (TauD (RetD r))))

SpinD : ∀ {R} -> Delay R
ValueD SpinD = TauD' SpinD

--------------------
-- Tree examples --
--------------------

--------------------
-- Itree examples --
--------------------

Echo : ITree IO Unit
ValueIT Echo = Vis (Input) λ x → Vis (Output x) λ x₁ → Tau' Echo

Spin : ITree IO Unit
ValueIT Spin = Tau' Spin

{-# NON_TERMINATING #-}
echo : itree IO Unit
echo = vis Input λ x → vis (Output x) λ _ → tau echo
