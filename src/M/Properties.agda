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
open import Cubical.Foundations.FunExtEquiv
open import Cubical.Foundations.Embedding
open import Cubical.Core.Glue
open import Cubical.Foundations.Equiv

open import helper

module M.Properties where

open import M.Base
open import Container

-- in-fun and out-fun are inverse

out-inverse-in : ∀ {ℓ} {S : Container {ℓ}} -> (out-fun {S = S} ∘ in-fun {S = S}) ≡ idfun (P₀ (M S))
out-inverse-in {S = S} i a = transport⁻Transport {A = P₀ {S = S} (M S)} {B = M S} (shift {S = S}) a i

in-inverse-out : ∀ {ℓ} {S : Container {ℓ}} -> (in-fun ∘ out-fun {S = S}) ≡ idfun (M S)
in-inverse-out {S = S} i a = transportTransport⁻ {A = P₀ (M S)} {B = M S} (shift {S = S}) a i

in-out-id : ∀ {ℓ} {S : Container {ℓ}} -> ∀ {x y} → (in-fun (out-fun {S = S} x) ≡ in-fun (out-fun {S = S} y)) ≡ (x ≡ y)
in-out-id {x = x} {y} =
  (in-fun (out-fun x) ≡ in-fun (out-fun y))
    ≡⟨ cong₂ _≡_ (funExt⁻ in-inverse-out x) (funExt⁻ in-inverse-out y) ⟩
  (x ≡ y) ∎

-- Embeddings

in-embedding : ∀ {ℓ} {S : Container {ℓ}} → isEmbedding {A = P₀ (M S)} {B = M S} (in-fun {S = S})
in-embedding = isEquiv→isEmbedding (equivIsEquiv (pathToEquiv shift))

out-embedding : ∀ {ℓ} {S : Container {ℓ}} → isEmbedding (out-fun {S = S})
out-embedding = isEquiv→isEmbedding (equivIsEquiv (pathToEquiv (sym shift)))

-- constructor properties

in-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → P₀ (M S)} -> (in-fun ∘ f ≡ in-fun ∘ g) ≡ (f ≡ g)
in-inj = ≡-rel-a-inj in-fun out-fun in-inverse-out out-inverse-in

in-inj-x : ∀ {ℓ} {S : Container {ℓ}} -> ∀ {x y : P₀ (M S)} -> (in-fun x ≡ in-fun y) ≡ (x ≡ y)
in-inj-x {ℓ} {S = S} {x = x} {y} =
  let tempx = λ {(lift tt) → x}
      tempy = λ {(lift tt) → y} in
  in-fun x ≡ in-fun y
      ≡⟨ isoToPath (iso (λ x₁ t → x₁)
                        (λ x₁ → x₁ (lift tt))
                        (λ b → refl)
                        (λ a → refl)) ⟩
  (∀ (t : Lift Unit) -> ((in-fun ∘ tempx) t ≡ (in-fun ∘ tempy) t))
    ≡⟨ funExtPath ⟩
  (in-fun ∘ tempx) ≡ (in-fun ∘ tempy)
    ≡⟨ in-inj ⟩
  tempx ≡ tempy
    ≡⟨ sym (funExtPath) ⟩  
  (∀ (t : Lift Unit) -> tempx t ≡ tempy t)
    ≡⟨ isoToPath (iso (λ x₁ → x₁ (lift tt))
                      (λ x₁ t → x₁)
                      (λ b → refl)
                      (λ a → refl)) ⟩
  x ≡ y ∎

out-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → M S} -> (out-fun ∘ f ≡ out-fun ∘ g) ≡ (f ≡ g)
out-inj = ≡-rel-b-inj in-fun out-fun in-inverse-out out-inverse-in

-- isInjectiveTransport
