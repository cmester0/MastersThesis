{-# OPTIONS --cubical --guardedness --safe #-}

module Coalg.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.Sigma

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.helper

open import Cubical.Codata.M.AsLimit.Coalg
open Cubical.Codata.M.AsLimit.Coalg public -- Re-export

-------------------------------
-- Definition of a Coalgebra --
-------------------------------

Coalg₁ : ∀ {ℓ} {S : Container ℓ} → Coalg₀ {S = S} → Coalg₀ {S = S} → Type ℓ
Coalg₁ {S = S} (C , γ) (D , δ) = Σ (C → D) λ f → δ ∘ f ≡ (P₁ f) ∘ γ

-- Coalgebra morphism notation
_⇒_ = Coalg₁
