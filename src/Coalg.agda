{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe
module Coalg where

open import M

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )

-- contractible (F is the final coalgebra)

Coalg₀ : ∀ {ℓ} {S : Container {ℓ}} -> Set (ℓ-suc ℓ)
Coalg₀ {ℓ} {S = S} = Σ (Set ℓ) λ C → C → P₀ {S = S} C  

Coalg₁ : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set ℓ
Coalg₁ {S = S} (C , γ) (D , δ) = Σ (C → D) λ f → δ ∘ f ≡ (P₁{S = S} f) ∘ γ

_⇒_ = Coalg₁

Final : ∀ {ℓ} {S : Container {ℓ}} -> Set (ℓ-suc ℓ)
Final {S = S} = Σ (Coalg₀ {S = S}) λ X,ρ → ∀ (C,γ : Coalg₀ {S = S}) -> isContr (_⇒_ {S = S} (C,γ) (X,ρ))

Ms : ∀ {ℓ} -> (S : Container {ℓ}) -> Container {ℓ}
Ms S = M S -,- λ x → P₀ {S = S} (M S)

M-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S}
M-coalg {S = S} = (M S) , out-fun

M-final-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Final {S = S}
M-final-coalg {S = S} = {!!} -- M-coalg {S = S} , λ C,γ → {!!} , λ y i → {!!} -- U is contractible

unfold : ∀ {ℓ} {S : Container {ℓ}} -> (X,ρ : Final {S = S}) -> (C,γ : Coalg₀ {S = S}) -> (C,γ .fst) -> (X,ρ .fst .fst)  -- unique function into final coalg
unfold X,ρ C,γ y = X,ρ .snd C,γ .fst .fst y

final-coalg-property : ∀ {ℓ} {S : Container {ℓ}} -> (F1 F2 : Final {S = S}) -> F1 ≡ F2
final-coalg-property  F1 F2 = λ i → {!!} -- follows from contractability ?

final-coalg-property-2 : ∀ {ℓ} {S : Container {ℓ}} -> (C : Coalg₀ {S = S}) -> (F : Final {S = S}) -> ∀ (f g : C ⇒ F .fst) -> f ≡ g
final-coalg-property-2 C F f g = λ i -> {!!} -- follows from contractability

-- bisimulation
record bisimulation {ℓ} (S : Container {ℓ}) (C,γ : Coalg₀ {S = S}) : Set (ℓ-suc ℓ) where  
  coinductive
  field R : C,γ .fst -> C,γ .fst -> Set ℓ
  R⁻ = Σ (C,γ .fst) (λ a -> Σ (C,γ .fst) (λ b -> R a b))

  π₁ : R⁻ -> C,γ .fst
  π₁ = fst
  
  π₂ : R⁻ -> C,γ .fst
  π₂ = fst ∘ snd
  
  field
    αᵣ : R⁻ -> P₀ {S = S} R⁻
    rel₁ : (C,γ .snd) ∘ π₁ ≡ P₁ π₁ ∘ αᵣ
    rel₂ : (C,γ .snd) ∘ π₂ ≡ P₁ π₂ ∘ αᵣ

  R⁻-coalg : Coalg₀
  R⁻-coalg = R⁻ , αᵣ
  
  prod₁ : R⁻-coalg ⇒ C,γ
  prod₁ = π₁ , rel₁
  
  prod₂ : R⁻-coalg ⇒ C,γ
  prod₂ = π₂ , rel₂

open bisimulation

open Container

final-property : ∀ {ℓ} (S : Container {ℓ}) -> (sim : bisimulation S M-coalg) -> prod₁ sim ≡ prod₂  sim
final-property S sim = final-coalg-property-2 (R⁻-coalg sim) M-final-coalg (prod₁ sim) (prod₂ sim)

final-property-2 : ∀ {ℓ} (S : Container {ℓ}) -> (sim : bisimulation S M-coalg) -> π₁ sim ≡ π₂  sim
final-property-2 S sim = λ i -> final-property S sim i .fst

coinduction : ∀ {ℓ} (S : Container {ℓ}) -> (sim : bisimulation S M-coalg) -> ∀ (m m' : M S) -> (R sim) m m' -> m ≡ m' -- m ≡ π₁(m,m',r) ≡ π₂(m,m',r) ≡ m'
coinduction S sim m m' r = λ i -> funExt⁻ (final-property-2 S sim) (m , (m' , r)) i

bisim-helper : ∀ {ℓ} {S : Container {ℓ}} -> bisimulation S M-coalg
bisim-helper {S = S} = record { R = _≡_ ; αᵣ = λ x → (out-fun {S = S} (x .fst) .fst) , λ x₁ → x .fst , x .snd ; rel₁ = λ i → λ a → {!!} , (λ x → {!!} , {!!}) ; rel₂ = {!!} }

-- Σ (M S .fst) (λ a -> Σ (M S .fst) (λ b -> a ≡ b))
-- Σ (M S .fst) (λ a -> Σ (M S .fst) (λ b -> R a b))

