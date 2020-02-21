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

Echo : ITree IO ⊥
ValueIT Echo = Vis (Input) λ x → Vis (Output x) λ _ → Tau' Echo

Spin : ITree IO ⊥
ValueIT Spin = Tau' Spin

{-# NON_TERMINATING #-}
echo : itree IO ⊥
echo = vis Input λ x → vis (Output x) λ _ → tau echo

{-# NON_TERMINATING #-}
echo2 : itree IO ⊥
echo2 = in-fun (vis2 Input λ x → vis2 (Output x) λ _ → tau' echo2)

{-# NON_TERMINATING #-}
spin2 : itree IO ⊥
spin2 = in-fun (tau' spin2)

{-# NON_TERMINATING #-}
echo3 : itree IO ⊥
echo3 = bind (trigger Input) λ x → bind (trigger (Output x)) λ { tt -> tau echo3 }

{-# NON_TERMINATING #-}
Echo2 : ITree IO ⊥
ValueIT Echo2 = Bind (Trigger Input) λ x → Bind (Trigger (Output x)) λ { tt -> Tau' Echo2 }

-- echo3 : Bind' (Trigger Input) λ x → Bind' (Trigger (Output x)) λ x₁ → Tau' Echo2
