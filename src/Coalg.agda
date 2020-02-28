{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe

open import M

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )

open import Cubical.Data.Unit

module Coalg where

Coalg₀ : ∀ {ℓ} {S : Container {ℓ}} -> Set (ℓ-suc ℓ)
Coalg₀ {ℓ} {S = S} = Σ (Set ℓ) λ C → C → P₀ {S = S} C  

Coalg₁ : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set ℓ
Coalg₁ {S = S} (C , γ) (D , δ) = Σ (C → D) λ f → δ ∘ f ≡ (P₁ f) ∘ γ

_⇒_ = Coalg₁

Ms : ∀ {ℓ} -> (S : Container {ℓ}) -> Container {ℓ}
Ms S = M S , λ x → P₀ {S = S}  (M S)

Ms2 : ∀ {ℓ} -> (S : Container {ℓ}) -> Container {ℓ}
Ms2 S = (P₀ {S = S} (M S)) , λ x → P₀ {S = S}  (P₀ {S = S}  (M S))

M-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S}
M-coalg {S = S} = (M S) , out-fun

PM-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S}
PM-coalg {S = S} = (P₀ (M S)) , P₁ out-fun

Final : ∀ {ℓ} {S : Container {ℓ}} -> Set (ℓ-suc ℓ)
Final {S = S} = Σ (Coalg₀ {S = S}) λ X,ρ → ∀ (C,γ : Coalg₀ {S = S}) -> isContr (_⇒_ {S = S} (C,γ) (X,ρ))


-- -- Bisimilarity as a coinductive record type.
-- record _≈_ {X : Type₀} {C : IxCont X} {x : X} (a b : M C x) : Type₀ where
--   coinductive
--   constructor _,_
--   field
--     head≈ : a .head ≡ b .head
--     tails≈ : ∀ y → (pa : C .snd x (a .head) y) (pb : C .snd x (b .head) y)
--              → (\ i → C .snd x (head≈ i) y) [ pa ≡ pb ]
--              → a .tails y pa ≈ b .tails y pb

-- record M {ℓ} {X : Type ℓ} (C : IxCont X) (x : X) : Type ℓ where -- Type₀
--   coinductive
--   field
--     head : C .fst x
--     tails : ∀ y → C .snd x head y → M C y

-- bisimulation2
record _≈_ {ℓ} {S : Container {ℓ}} (a b : M S) : Set (ℓ-suc ℓ) where
  coinductive
  field
    head≈ : out-fun a .fst ≡ out-fun b .fst
    tails≈ : ∀ (pa : S .snd (out-fun a .fst)) (pb : S .snd (out-fun b .fst)) -> out-fun {S = S} a .snd pa ≈ out-fun {S = S} b .snd pb

open _≈_ public

-- bisimulation
record bisimulation {ℓ} (S : Container {ℓ}) (C,γ : Coalg₀ {S = S}) (R : C,γ .fst -> C,γ .fst -> Set ℓ) : Set (ℓ-suc ℓ) where  
  coinductive
  -- field R : C,γ .fst -> C,γ .fst -> Set ℓ
  
  R⁻ = Σ (C,γ .fst) (λ a -> Σ (C,γ .fst) (λ b -> R a b))

  π₁ : R⁻ -> C,γ .fst
  π₁ = fst
  
  π₂ : R⁻ -> C,γ .fst
  π₂ = fst ∘ snd
  
  field
    αᵣ : R⁻ -> P₀ {S = S} R⁻
    rel₁ : (C,γ .snd) ∘ π₁ ≡ P₁ π₁ ∘ αᵣ
    rel₂ : (C,γ .snd) ∘ π₂ ≡ P₁ π₂ ∘ αᵣ

  -- R⁻-coalg : Coalg₀
  -- R⁻-coalg = R⁻ , αᵣ
  
  -- prod₁ : R⁻-coalg ⇒ C,γ
  -- prod₁ = π₁ , rel₁
  
  -- prod₂ : R⁻-coalg ⇒ C,γ
  -- prod₂ = π₂ , rel₂

open bisimulation public

-- unfold : ∀ {ℓ} {S : Container {ℓ}} -> (X,ρ : Final {S = S}) -> (C,γ : Coalg₀ {S = S}) -> (_⇒_ {S = S} (C,γ) (X,ρ .fst))  -- unique function into final coalg
-- unfold X,ρ C,γ = X,ρ .snd C,γ .fst

-- unfold-function : ∀ {ℓ} {S : Container {ℓ}} -> (X,ρ : Final {S = S}) -> (C,γ : Coalg₀ {S = S}) -> (C,γ .fst) -> (X,ρ .fst .fst)  -- unique function into final coalg
-- unfold-function X,ρ C,γ y = (unfold X,ρ C,γ) .fst y

-- U : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Set ℓ
-- U {S = S} {C,γ = C,γ} = Σ (C,γ .fst -> M S) λ f → out-fun ∘ f ≡ P ₁ f ∘ C,γ .snd

-- -- transp-and-back : ∀ {ℓ} {A B : Set ℓ} (f : A ≡ B) -> transport (sym f) ∘ transport f ≡ (λ x -> x)
-- -- transp-and-back f = λ i -> {!!}

-- -- in-out-inv : ∀ {ℓ} {S : Container {ℓ}} -> (in-fun ∘ out-fun {S = S}) ≡ λ x -> x
-- -- in-out-inv = λ i a → transp (λ i → shift {S = S} i) i0 (transp (λ i → shift {S = S} (~ i)) i0 a)

-- -- U-is-Unit : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> (U {C,γ = C,γ} ≡ Lift Unit)
-- -- U-is-Unit = λ i → {!!}

-- postulate -- TODO
--   U-is-Unit : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> (U {C,γ = C,γ} ≡ Lift Unit)

-- contr-is-ext : ∀ {ℓ} {A B : Set ℓ} -> A ≡ B -> isContr A ≡ isContr B
-- contr-is-ext p = λ i -> isContr (p i)

-- -- postulate
-- --   U-contr : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ∀ (x : U {C,γ = C,γ}) -> isContr (U {C,γ = C,γ})
  
-- U-contr : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ∀ (x : U {C,γ = C,γ}) -> isContr (U {C,γ = C,γ})
-- U-contr x = transp (λ i -> (sym (contr-is-ext U-is-Unit)) i) i0 (lift tt , λ { (lift tt) -> refl })

-- -- Finality
-- M-final-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Final {S = S}
-- M-final-coalg {S = S} = M-coalg , λ C,γ → transp (λ i → (sym U-is-Unit) i) i0 (lift tt) , λ y → U-contr {C,γ = C,γ} y .snd y

-- final-coalg-property : ∀ {ℓ} {S : Container {ℓ}} -> (F1 F2 : Final {S = S}) -> F1 ≡ F2
-- final-coalg-property  F1 F2 = λ i → {!!}

-- final-coalg-property-2 : ∀ {ℓ} {S : Container {ℓ}} -> (C : Coalg₀ {S = S}) -> (F : Final {S = S}) -> ∀ (f g : C ⇒ F .fst) -> f ≡ g
-- final-coalg-property-2 C F f g = λ i -> compPath-filler (sym (F .snd C .snd f))  (F .snd C .snd g) i i -- follows from contractability

-- final-property : ∀ {ℓ} (S : Container {ℓ}) -> (sim : bisimulation S M-coalg) -> prod₁ sim ≡ prod₂  sim
-- final-property S sim = final-coalg-property-2 {S = S} (R⁻-coalg sim) (M-final-coalg {S = S}) (prod₁ sim) (prod₂ sim)

-- final-property-2 : ∀ {ℓ} (S : Container {ℓ}) -> (sim : bisimulation S M-coalg) -> π₁ sim ≡ π₂  sim
-- final-property-2 S sim = λ i -> final-property S sim i .fst

-- coinduction : ∀ {ℓ} (S : Container {ℓ}) -> (sim : bisimulation S M-coalg) -> ∀ (m m' : M S) -> (R sim) m m' -> m ≡ m' -- m ≡ π₁(m,m',r) ≡ π₂(m,m',r) ≡ m'
-- coinduction S sim m m' r = λ i -> funExt⁻ (final-property-2 S sim) (m , (m' , r)) i

-- bisim-helper : ∀ {ℓ} {S : Container {ℓ}} -> bisimulation S M-coalg
-- bisim-helper {S = S} = record { R = _≡_ ; αᵣ = {!!} ; rel₁ = {!!} ; rel₂ = {!!} }

