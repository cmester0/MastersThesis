{-# OPTIONS --cubical --guardedness #-} --safe

module state-machine where

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Transport

open import M
open import helper
open import Container
open import Container-M-type
open import Coalg

open import Cubical.Functions.Embedding

open import Cubical.Foundations.Path

data ⊥-ℓ {ℓ} : Set ℓ where 

state-container : ∀ {ℓ} (token : Set ℓ) (state : Set ℓ) → Container {ℓ}
state-container token state = state × (state → token → state) , λ x → ⊥-ℓ
-- state , 

state-machine-M : ∀ {ℓ} token state-space → Set ℓ
state-machine-M token state-space = M (state-container token state-space)

make-automaton : ∀ {ℓ} {token : Set ℓ} {state : Set ℓ} → state → (state → token → state) → state-machine-M token state
make-automaton {token} {state} x y = in-fun ((x , y) , λ ())

step-state : ∀ {ℓ} {token : Set ℓ} {state : Set ℓ} → token → state-machine-M token state → state-machine-M token state
step-state {token = token} {state} p = M-coinduction-const (state-machine-M token state) (λ {((x , y) , b) → in-fun ((y x p , y) , λ ())})

data ab-lang : Set where
  a : ab-lang
  b : ab-lang

data last-sym-state : Set where
  la : last-sym-state
  lb : last-sym-state

aælsdf = step-state b (make-automaton {token = ab-lang} la λ {_ a → la ; _ b → lb})


