{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Foundations.Transport

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Core.Glue
open import Cubical.Foundations.Equiv

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding

open import helper

module M.Properties where

open Iso

open import M.Base
open import Container

-- in-fun and out-fun are inverse

in-inverse-out :
  ∀ {ℓ} {S : Container {ℓ}} →
  (in-fun ∘ out-fun) ≡ idfun (M S)
in-inverse-out {S = S} = funExt (rightInv {A = P₀ (M S)} {B = M S} (shift-iso {S = S}))

out-inverse-in :
  ∀ {ℓ} {S : Container {ℓ}} →
  (out-fun ∘ in-fun) ≡ idfun (P₀ (M S))
out-inverse-in {S = S} = funExt (leftInv {A = P₀ {S = S} (M S)} {B = M S} (shift-iso {S = S}))

in-out-id :
  ∀ {ℓ} {S : Container {ℓ}} →
  ∀ {x y} →
  (in-fun (out-fun {S = S} x) ≡ in-fun (out-fun y)) ≡ (x ≡ y)
in-out-id {S = S} {x = x} {y} i = (in-inverse-out i x) ≡ (in-inverse-out i y)

-- Embeddings

-- in-embedding :
--   ∀ {ℓ} {S : Container {ℓ}} → 
--   isEmbedding (in-fun {S = S})
-- in-embedding {S = S} = ≡-to-embedding {A = P₀ (M S)} {C = M S} shift-iso 

-- out-embedding :
--   ∀ {ℓ} {S : Container {ℓ}} →
--   isEmbedding (out-fun {S = S})
-- out-embedding {S = S} = ≡-to-embedding {A = M S} {C = P₀ {S = S} (M S)} (sym-iso shift-iso)
 
-- constructor properties

in-inj :
  ∀ {ℓ} {S : Container {ℓ}} →
  {Z : Set ℓ}
  → ∀ {f g : Z → P₀ (M S)}
  → (in-fun ∘ f ≡ in-fun ∘ g) ≡ (f ≡ g)
in-inj {ℓ} {S = S} {Z = Z} {f = f} {g = g} =
  ≡-rel-a-inj {ℓ = ℓ} {A = P₀ (M S)} {B = M S} {C = Z} (shift-iso) {f = f} {g = g}

out-inj :
  ∀ {ℓ} {S : Container {ℓ}} →
  {Z : Set ℓ} →
  ∀ {f g : Z → M S}
  → (out-fun ∘ f ≡ out-fun ∘ g) ≡ (f ≡ g)
out-inj {ℓ} {S = S} {Z = Z} {f = f} {g = g} =
  ≡-rel-b-inj {ℓ = ℓ} {A = P₀ (M S)} {B = M S} {C = Z} (shift-iso) {f = f} {g = g}

in-inj-x :
  ∀ {ℓ} {S : Container {ℓ}} →
  ∀ {x y : P₀ (M S)}
  → (in-fun x ≡ in-fun y) ≡ (x ≡ y)
in-inj-x {ℓ} {S = S} {x = x} {y} = ≡-rel-a-inj-x shift-iso

out-inj-x :
  ∀ {ℓ} {S : Container {ℓ}} →
  ∀ {x y : M S}
  → (out-fun x ≡ out-fun y) ≡ (x ≡ y)
out-inj-x {ℓ} {S = S} {x = x} {y} = ≡-rel-b-inj-x shift-iso
