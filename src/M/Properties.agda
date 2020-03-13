{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )

open import Cubical.Foundations.Transport

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Sum

open import helper

module M.Properties where

open import M.Base
open import Container

-- -- in-fun and out-fun are inverse

postulate -- TODO: Slow computations..
  out-inverse-in : ∀ {ℓ} {S : Container {ℓ}} -> (out-fun ∘ in-fun {S = S}) ≡ idfun (P₀ (M S))
-- out-inverse-in {S = S} i a = transport⁻Transport {A = P₀ (M S)} {B = M S} (shift {S = S}) a i

postulate -- TODO: Slow computations..
  in-inverse-out : ∀ {ℓ} {S : Container {ℓ}} -> (in-fun ∘ out-fun {S = S}) ≡ idfun (M S)
-- in-inverse-out {S = S} i a = transportTransport⁻ {A = P₀ (M S)} {B = M S} (shift {S = S}) a i

-- -- constructor properties

postulate -- TODO: Slow computations..
  in-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → P₀ (M S)} -> (in-fun ∘ f ≡ in-fun ∘ g) ≡ (f ≡ g)
-- cxin-inj = ≡-rel-a-inj in-fun out-fun in-inverse-out out-inverse-in

-- out-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → M S} -> (out-fun ∘ f ≡ out-fun ∘ g) ≡ (f ≡ g)
-- out-inj = ≡-rel-b-inj in-fun out-fun in-inverse-out out-inverse-in

-- ---------------------------
-- -- Properties of M-types --
-- ---------------------------

-- Container-product : ∀ {ℓ} (_ _ : Container {ℓ}) -> Container {ℓ}
-- Container-product (A , B) (C , D) = (A × C , λ x → B (proj₁ x) × D (proj₂ x) )

-- P-product :
--   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--   -> ((n : ℕ) -> W (A , B) n) × ((n : ℕ) -> W (C , D) n)
--   ------------------------
--   -> (n : ℕ) -> W (Container-product (A , B) (C , D)) n
-- P-product (x , y) 0 = lift tt
-- P-product (x , y) (suc n) = ((x (suc n) .fst) , (y (suc n) .fst)) , λ _ → P-product (x , y) n

-- P-product-inv₁ :
--   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--   -> ((n : ℕ) -> W (Container-product (A , B) (C , D)) n)
--   ------------------------
--   -> (n : ℕ) -> W (A , B) n
-- P-product-inv₁ x 0 = lift tt
-- P-product-inv₁ {D = D} x (suc n) = (proj₁ (x (suc n) .fst)) , (λ _ → P-product-inv₁ {D = D} x n)

-- P-product-inv₂ :
--   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--   -> ((n : ℕ) -> W (Container-product (A , B) (C , D)) n)
--   ------------------------
--   -> (n : ℕ) -> W (C , D) n
-- P-product-inv₂ x 0 = lift tt
-- P-product-inv₂ {B = B} x (suc n) = (proj₂ (x (suc n) .fst)) , (λ _ → P-product-inv₂ {B = B} x n)

-- P-product-inv :
--   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--   -> ((n : ℕ) -> W (Container-product (A , B) (C , D)) n)
--   ------------------------
--   -> ((n : ℕ) -> W (A , B) n) × ((n : ℕ) -> W (C , D) n)  
-- P-product-inv {B = B} {D = D} x = (P-product-inv₁ {D = D} x) , (P-product-inv₂ {B = B} x)

-- Product-split : ∀ {ℓ} {A B : Set ℓ} {x : A × B} -> ((proj₁ x , proj₂ x) ≡ x)
-- Product-split {x = a , b} = refl

-- postulate
--   Σ-prod-fun :
--     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--     → (n : ℕ)
--     → (x : A × C) 
--     → (B (proj₁ x) → W (A , B) n) × (D (proj₂ x) → W (C , D) n)
--     ≡ (B (proj₁ x) × D (proj₂ x) → W (A , B) n × W (C , D) n)

-- P-equality :
--     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--     -> (n : ℕ)
--     ------------------------
--     -> (W (A , B) n × W (C , D) n)
--     ≡ (W (Container-product (A , B) (C , D)) n)
-- P-equality {A = A} {C} {B} {D} 0 = isoToPath (iso (λ _ → lift tt) (λ _ → lift tt , lift tt) (λ b i → lift tt) (λ {(_ , _) i → (lift tt) , (lift tt)}))
-- P-equality {A = A} {C} {B} {D} (suc n) =
--   W (A , B) (suc n) × W (C , D) (suc n)
--     ≡⟨ refl ⟩
--   Σ A (λ a → B a → W (A , B) n) × Σ C (λ c → D c → W (C , D) n)
--     ≡⟨ isoToPath (iso (λ {((a , c) , (b , d)) → (a , b) , (c , d)})
--                       (λ {((a , c) , (b , d)) → (a , b) , (c , d)})
--                       (λ {((a , c) , (b , d)) → refl})
--                       (λ { ((a , c) , b , d) → refl })) ⟩
--   Σ (A × C) (λ {(a , c) → (B a → W (A , B) n) × (D c → W (C , D) n)})
--     ≡⟨ Σ-ap-iso₂ (λ {(a , c) → Σ-prod-fun {A = A} {C = C} {B = B} {D = D} n (a , c)}) ⟩
--   Σ (A × C) (λ {(a , c) → B a × D c → W (A , B) n × W (C , D) n})
--     ≡⟨ Σ-ap-iso₂ (λ {(a , c) i → B a × D c → P-equality {B = B} {D = D} n i}) ⟩
--   Σ (A × C) (λ {(a , c) → B a × D c → W (Container-product (A , B) (C , D)) n})
--     ≡⟨ Σ-ap-iso₂ (λ {(a , c) → refl}) ⟩
--   W (Container-product (A , B) (C , D)) (suc n) ∎

-- postulate
--   π-equality :
--     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--     -> (x : (n : ℕ) -> W (Container-product (A , B) (C , D)) n)
--     -> (n : ℕ)
--     ------------------------
--     -> πₙ (Container-product (A , B) (C , D)) (x (suc n))
--     ≡ x n

--   π-equality-2₁ :
--     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--     -> (x : (n : ℕ) -> W (A , B) n × W (C , D) n)
--     -> (n : ℕ)
--     -----------------------
--     -> πₙ (A , B) (proj₁ (x (suc n)))
--     ≡ proj₁(x n)

--   π-equality-2₂ :
--     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
--     -> (x : (n : ℕ) -> W (A , B) n × W (C , D) n)
--     -> (n : ℕ)
--     -----------------------
--     -> πₙ (C , D) (proj₂ (x (suc n)))
--     ≡ proj₂(x n)

-- M-product : ∀ {ℓ} S T -> M {ℓ = ℓ} S × M T -> M (Container-product S T)
-- M-product S T (x , y) = (λ n → transport (P-equality n) (x .fst n , y .fst n)) , π-equality {B = S .snd} {D = T .snd} (λ n -> transport (P-equality n) (x .fst n , y .fst n))

-- M-product-inv : ∀ {ℓ} S T -> M (Container-product S T) -> M {ℓ = ℓ} S × M T
-- M-product-inv S T (x , y) = ((λ n → proj₁ (transport (sym (P-equality {B = S .snd} {D = T .snd} n)) (x n))) ,
--                                 π-equality-2₁ {B = S .snd} {D = T .snd} (λ n → transport (λ i → P-equality {B = S .snd} {D = T .snd} n (~ i)) (x n))) ,
--                              (λ n → proj₂ (transport (sym (P-equality {B = S .snd} {D = T .snd} n)) (x n))) ,
--                                 π-equality-2₂ {B = S .snd} {D = T .snd} (λ n → transport (λ i → P-equality {B = S .snd} {D = T .snd} n (~ i)) (x n))

-- postulate
--   M-product-iso₁ : ∀ {ℓ} (S T : Container {ℓ}) b -> M-product S T (M-product-inv S T b) ≡ b
--   M-product-iso₂ : ∀ {ℓ} (S T : Container {ℓ}) a -> M-product-inv S T (M-product S T a) ≡ a

-- M-product-equality : ∀ {ℓ} S T -> M {ℓ = ℓ} S × M T ≡ M (Container-product S T)
-- M-product-equality S T = isoToPath (iso (M-product S T) (M-product-inv S T) (M-product-iso₁ S T) (M-product-iso₂ S T))

-- ---------------------------
-- -- Function into M-types --
-- ---------------------------

