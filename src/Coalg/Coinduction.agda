{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Prod

open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Embedding

open import helper

module Coalg.Coinduction where

open import Coalg.Base
open import Coalg.Properties
open import Container
open import M

-------------------------------
-- Bisimilarity of Coalgebra --
-------------------------------

-- Strong bisimulation ?
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

  R⁻-coalg : Coalg₀
  R⁻-coalg = R⁻ , αᵣ

  prod₁ : R⁻-coalg ⇒ C,γ
  prod₁ = π₁ , rel₁

  prod₂ : R⁻-coalg ⇒ C,γ
  prod₂ = π₂ , rel₂

open bisimulation public

final-property : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> prod₁ sim ≡ prod₂  sim
final-property S R sim = final-coalg-property-2 {S = S} (R⁻-coalg sim) (M-final-coalg {S = S}) (prod₁ sim) (prod₂ sim)

final-property-2 : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> π₁ sim ≡ π₂  sim
final-property-2 S R sim = cong fst (final-property S R sim)

R-bar : ∀ {ℓ} (S : Container {ℓ}) (R : M S → M S → Set ℓ) → Set ℓ
R-bar S R = Σ (M S) (λ a → Σ (M S) (λ b → R a b))

α-R : ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ)
  → (∀ {x} -> R x x)
  → R-bar S R → P₀ {S = S} (R-bar S R)
α-R S R R-refl ( a , b , r ) = out-fun a .fst , λ x → a , (b , r)
 -- fst (out-fun a) , λ x → (snd (out-fun a) x) , ((snd (out-fun a) x) , R-refl)

R-bar-coalg : ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ) → (∀ {x} -> R x x) → Coalg₀
R-bar-coalg S R R-refl = R-bar S R , α-R S R R-refl

-------------------------------------------------------------
-- Coinduction principle for M-types (≈ Coinductive types) --
-------------------------------------------------------------

-- coinduction proof by: m ≡ π₁(m,m',r) ≡ unfold-R ≡ π₂(m,m',r) ≡ m'
coinduction : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> ∀ {m m' : M S} -> R m m' -> m ≡ m'
coinduction {S = S} R sim {m} {m'} r = funExt⁻ (final-property-2 S R sim) (m , (m' , r))

coinduction⁻ : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (∀ {x} -> R x x) ->  ∀ {m m' : M S} -> m ≡ m' -> R m m'
coinduction⁻ {S = S} R sim k {m} {m'} r = subst (R m) r k

-- Equvalence-to-R-eq :
--   ∀ {ℓ} (S : Container {ℓ})
--   → (R : M S -> M S -> Set ℓ)
--   → (R-refl : ∀ {x} -> R x x)
--   → (∀ {x y z} -> R x y → R y z → R x z)
--   → (∀ {x y} -> R x y → R y x)
--   → (((a , b , _) : R-bar S R) → a ≡ b)
-- Equvalence-to-R-eq {ℓ} S R R-refl R-trans R-sym (a , b , r) =
--   let temp : {!!}
--       temp = {!!}
--   in
--     {!!}
--   where
--     postulate
--       aembed : isEmbedding (R a)


-- bisimulation-property :
--   ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ)
--   → (∀ {x} -> R x x)
--   → (∀ (a : M S) (x : S .snd (out-fun a .fst)) → out-fun a .snd x ≡ a)
--   → ((x : Σ (M S) (λ a → Σ (M S) (R a))) → fst x ≡ fst (snd x))
--   ------------------------------
--   → bisimulation S M-coalg R
-- αᵣ (bisimulation-property S R R-refl _ _) (a , b , r) = α-R S R R-refl (a , b , r)
-- rel₁ (bisimulation-property S R R-refl R-rel-1 R-eq) i (a , b , r) =
--   (out-fun a
--     ≡⟨ refl ⟩
--   (out-fun a .fst , λ x → out-fun a .snd x)
--     ≡⟨ (λ j → out-fun a .fst , λ x → R-rel-1 a x j) ⟩
--   (out-fun a .fst , λ x → a) ∎) i
-- rel₂ (bisimulation-property S R R-refl _ R-eq) i (a , b , r) =
--   (out-fun b
--     ≡⟨ {!!} ⟩
--   (out-fun a .fst , λ x → b) ∎) i

-- M-coalg .snd ∘ fst ≡ P₁ fst ∘ αᵣ (bisimulation-property S R R-refl R-eq)
-- M-coalg .snd ∘ fst ∘ snd ≡ P₁ (fst ∘ snd) ∘ αᵣ (bisimulation-property S R R-refl R-eq)

-- bisimulation-property :
--   ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ)
--   → (∀ {x} -> R x x)
--   → ((x : Σ (M S) (λ a → Σ (M S) (R a))) → fst x ≡ fst (snd x))
--   ------------------------------
--   → bisimulation S M-coalg R
-- αᵣ (bisimulation-property S R R-refl _) (a , b , r) = α-R S R R-refl (a , b , r)
-- rel₁ (bisimulation-property _ _ _ R-eq) i (a , b , r) = out-fun a
-- rel₂ (bisimulation-property S R R-refl R-eq) i (a , b , r) =
--   -- (R-eq (a , b , r))
--   let temp : a ≡ b
--       temp = {!!}
--   in
--   transport (sym out-inj-x) temp (~ i)
--   where
--     postulate
--       R-trans : (∀ {x y z} -> R x y → R y z → R x z)
--       R-antisym : (∀ {x y} -> R x y → R y x → x ≡ y)
--       R-sym : (∀ {x y} -> R x y → R y x)

  -- (out-fun b
  --   ≡⟨ {!!} ⟩
  -- out-fun a ∎) i
-- out-fun b ≡ out-fun a -> a ≡ b

-- (a , b , r)
-- α-R S R R-refl ( a , b ) = fst (out-fun a) , λ x → (snd (out-fun a) x) , ((snd (out-fun a) x) , R-refl)

-- out-fun (R-eq (a , b , r) (~ i))
-- out-fun b ≡⟨ {!!} ⟩ out-fun a ∎ -- cong out-fun (sym {!!}) -- (R-eq x) -- rel₁ : out-fun ∘ snd ≡ P₁ snd ∘ αᵣ

-- M-coalg .snd ∘ fst ∘ snd ≡ P₁ (fst ∘ snd) ∘ αᵣ (bisimulation-property S R x R-eq)
-- M-coalg .snd ∘ fst ∘ snd ≡ P₁ (fst ∘ snd) ∘ α-R S R R-refl x

-- (out-fun b)
-- (λ x → (snd (out-fun a) x))

-- postulate
--   coinduction-iso1 :
--     ∀ {ℓ} {S : Container {ℓ}} R
--     → (sim : bisimulation S M-coalg R)
--     → (R-refl : ∀ {x} -> R x x) →
--     ∀ {m} {m'} (p : m ≡ m')
--     → (coinduction R sim {m} {m'}) (coinduction⁻ R sim R-refl p) ≡ p
    
-- postulate
--   coinduction-iso2 :
--     ∀ {ℓ} {S : Container {ℓ}} R
--     → (sim : bisimulation S M-coalg R)
--     → (R-refl : ∀ {x} -> R x x) →
--     ∀ {m} {m'} (p : R m m')
--     → (coinduction⁻ R sim R-refl (coinduction R sim {m} {m'} p)) ≡ p

-- coinduction-is-equality : ∀ {ℓ} {S : Container {ℓ}} R ->
--   (sim : bisimulation S M-coalg R) ->
--   (R-refl : ∀ {x} -> R x x) ->
--   R ≡ _≡_
-- coinduction-is-equality R sim R-refl =
--   funExt λ m →
--   funExt λ m' →
--     isoToPath (iso
--       (coinduction R sim {m} {m'})
--       (coinduction⁻ R sim R-refl)
--       (coinduction-iso1 R sim R-refl)
--       (coinduction-iso2 R sim R-refl))

-- ----------------
-- -- CoFixpoint --
-- ----------------
