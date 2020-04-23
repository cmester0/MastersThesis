{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetQuotients

open import Container
open import Coalg
open import itree

module QIIT where

-- data wq {ℓ} (A C : Set ℓ) (B : A → Set ℓ) (l r : C → A) : Set ℓ where
--   point-w :
--     (a : A) → (B a → wq A C B l r) → wq A C B l r
--   cell-w :
--     (c : C) →
--     (t : B (l c) → wq A C B l r) →
--     (s : B (r c) → wq A C B l r) →
--     (point-w (l c) t ≡ point-w (r c) s)

data mq {ℓ} (S : Container {ℓ}) (C : Set ℓ) (l r : C → S .fst) : Set ℓ where
  point-m :
    (a : S .fst) → (S .snd a → mq S C l r) → mq S C l r
  cell-m :
    (c : C) →
    (t : S .snd (l c) → mq S C l r) →
    (s : S .snd (r c) → mq S C l r) →
    (point-m (l c) t ≡ point-m (r c) s)

asdkds : ∀ R → mq (delay-S R) (delay R) (λ x → M-coalg .snd x .fst) (λ x → M-coalg .snd (delay-tau x) .fst)
asdkds R = point-m {!!} {!!}

-- mq = M-coalg
-- ε (asdkds R) = delay R , ((λ _ → delay R) , (λ e → record { η = delay-tau e ; σ = {!!} }) , λ e → record { η = e ; σ = {!!} })
-- qmequ (asdkds R) e ρ = {!!} -- funExt λ x → {!!}

-- record T {ℓ} {S : Container {ℓ}} (X : Set ℓ) : Set (ℓ-suc ℓ) where
--   coinductive
--   field
--     η : X
--     σ : P₀ {S = S} X
  
-- open T

-- _>>=_ : ∀ {ℓ} {S : Container {ℓ}} {X Y} -> T {S = S} X → (f : X → Y) → T {S = S} Y
-- η (t >>= f) = f (η t)
-- σ (t >>= f) = P₁ f (σ t)

-- equation-system : ∀ {ℓ : Level} {S : Container {ℓ}} → Set (ℓ-suc ℓ) 
-- equation-system {ℓ} {S = S} = Σ (Set ℓ) (λ E → Σ (E → Set ℓ) (λ V → ((e : E) → T {S = S} (V e)) × ((e : E) → T {S = S} (V e)))) -- free V e-coalgebra ?

-- sat : ∀ {ℓ} {S : Container {ℓ}} → Coalg₀ {S = S} → equation-system {S = S} → Set (ℓ-suc ℓ)
-- sat C,γ (E , V , l , r) = (e : E) → (ρ : V e → C,γ .fst) → ((l e) >>= ρ) ≡ ((r e) >>= ρ)

-- record QM-type {ℓ : Level} (S : Container {ℓ}) : Set (ℓ-suc ℓ) where
--   field
--     QM : Coalg₀ {S = S}
--     ε : equation-system
--     qmequ : sat QM ε

-- open QM-type

-- -- This should be a final coalgebra ! (todo add constructors, forcing that, or show this is the case)
-- rdgftb : forall R -> (∀ (t : delay R) → t ≡ delay-tau t) -> QM-type (delay-S R)
-- QM (rdgftb R h) = M-coalg
-- ε (rdgftb R h) = delay R , (λ x → delay R) , (λ e → record { η = e ; σ = M-coalg .snd e }) , λ e → record { η = delay-tau e ; σ = M-coalg .snd e }
-- η (qmequ (rdgftb R h) e ρ i) = ρ (h e i)
-- σ (qmequ (rdgftb R h) e ρ i) = P₁ ρ (M-coalg .snd e)

-- -- Some basic properties of QM-types, the quotiented relation, becomes a bisimulation relation?
-- adsgfj : {ℓ : Level} {S : Container {ℓ}} (q : QM-type S) → bisimulation S (QM q) {!!}
-- αᵣ (adsgfj q) x = QM q .snd (x .fst) .fst , (λ x₁ → x .fst , x .snd .fst , {!!})
-- rel₁ (adsgfj q) = {!!}
-- rel₂ (adsgfj q) = {!!}

-- -- Basically the construction of the partiality monad, some kinks to work out!

-- -- asdkds : ∀ R → QM-type (delay-S R)
-- -- QM (asdkds R) = M-coalg
-- -- ε (asdkds R) = delay R , ((λ _ → delay R) , (λ e → record { η = delay-tau e ; σ = {!!} }) , λ e → record { η = e ; σ = {!!} })
-- -- qmequ (asdkds R) e ρ = {!!} -- funExt λ x → {!!}



-- -- record partiality-monad {A : Set} : Set₁ where
-- --   field
-- --     A⊥ : Set
-- --     _⊑_ : A⊥ → A⊥ → Set

-- --     η : A → A⊥
-- --     ⊥ₐ : A⊥
-- --     ⊔ : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)) → A⊥
-- --     α : (x y : A⊥) → x ⊑ y → y ⊑ x → x ≡ y

-- --     ⊑-refl : ∀ {x : A⊥} → x ⊑ x
-- --     ⊑-trans : ∀ {x y z : A⊥} → x ⊑ y → y ⊑ z → x ⊑ z
-- --     ⊑-⊥ : ∀ {x} → ⊥ₐ ⊑ x

-- --     ⊑-prop : isProp ({x y : A⊥} → x ⊑ y)
-- --     ⊑-0 : {(s , p) : Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)} → (n : ℕ) → s n ⊑ ⊔ (s , p)
-- --     ⊑-1 : {(s , p) : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n))} → (x : A⊥) → (n : ℕ) → s n ⊑ x → ⊔ (s , p) ⊑ x

-- -- open partiality-monad

-- -- record partiality-algebra (A : Set) : Set₁ where
-- --   field
-- --     X : Set
-- --     _⊑ₓ_ : X → X → Set
-- --     ⊥ₓ : X
-- --     ηₓ : A → X
-- --     ⊔ₓ : (Σ (ℕ → X) λ s → (n : ℕ) → s n ⊑ₓ s (suc n)) → X

-- --     ⊑ₓ-refl : ∀ {x : X} → x ⊑ₓ x
-- --     ⊑ₓ-trans : ∀ {x y z : X} → x ⊑ₓ y → y ⊑ₓ z → x ⊑ₓ z
-- --     ⊑ₓ-antisym : ∀ {x y : X} → x ⊑ₓ y → y ⊑ₓ x → x ≡ y
-- --     ⊑ₓ-⊥ : ∀ {x} → ⊥ₓ ⊑ₓ x

-- --     ⊑ₓ-prop : isProp ({x y : X} → x ⊑ₓ y)
-- --     ⊑ₓ-0 : ((s , p) : Σ (ℕ → X) λ s → (n : ℕ) → s n ⊑ₓ s (suc n)) → (n : ℕ) → s n ⊑ₓ ⊔ₓ (s , p)
-- --     ⊑ₓ-1 : ((s , p) : (Σ (ℕ → X) λ s → (n : ℕ) → s n ⊑ₓ s (suc n))) → (x : X) → (n : ℕ) → s n ⊑ₓ x → ⊔ₓ (s , p) ⊑ₓ x

-- -- open partiality-algebra

-- -- -- TODO : D(A)/∼D

-- -- ω-cpo : Set₁
-- -- ω-cpo = partiality-algebra ⊥ 

-- -- -- U : ω-cpo → Set
-- -- -- U x = X x

-- -- postulate
-- --   F : Set → ω-cpo

-- -- U-partiality-algebra : ∀ x → partiality-algebra ⊥
-- -- U-partiality-algebra x = x


