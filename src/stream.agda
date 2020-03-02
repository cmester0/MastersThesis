{-# OPTIONS --cubical --guardedness #-} --safe

module stream where

open import M

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Later
open import Cubical.Data.List
open import Cubical.Foundations.Univalence

open import Agda.Builtin.Coinduction

--------------------------------------
-- Stream definitions using M-types --
--------------------------------------

stream-S : ∀ A -> Container
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Set₀) -> Set₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

------------------------------------------------------------------------
-- Wrapping the stream definition to satisfy the termination checker? --
------------------------------------------------------------------------

scons : ∀ {A} -> A -> ∞ (stream A) -> ∞ (stream A)
scons a b = ♯ cons a (♭ b)

---------------------------------------------
-- Stream definitions using Later modality --
---------------------------------------------

record S (A : Set) : Set where
  inductive
  constructor _,_
  field
    headS : A
    tailS : ▹ (S A)

open S
