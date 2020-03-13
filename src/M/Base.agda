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
open import Container

open import Coalg.Base

module M.Base where

-----------------------
-- Equivalence Rules --
-----------------------

M-combine-helper :
  ∀ {ℓ} (X : ℕ -> Set ℓ)
  -> X 0
  -> ((n : ℕ) -> X (suc n))
  ---------------------
  -> (n : ℕ) -> X n
M-combine-helper X a b 0 = a
M-combine-helper X a b (suc n) = b n

M-combine-helper-lemma : ∀ {ℓ} (X : ℕ -> Set ℓ) (x : (n : ℕ) -> X n) (n : ℕ) -> (M-combine-helper X (x 0) (λ (n : ℕ) -> x (suc n)) n) ≡ x n
M-combine-helper-lemma X x 0 = refl
M-combine-helper-lemma X x (suc n) = refl

--------------------------------
-- Limit of a Chain is Unique --
--------------------------------

-- Lemma 12
L-unique : ∀ {ℓ} -> {S : Container {ℓ}} -> L (shift-chain (sequence S)) ≡ L (sequence S)
L-unique {ℓ} {S = S} =
  L (shift-chain (sequence S))
    ≡⟨ (isoToPath (iso (λ {(x , y) → π (sequence S) (x 0) , x , refl , y})
                       (λ x → x .snd .fst , proj₂ (x .snd .snd))
                       (λ {(x , y , z , w)  → λ i → x , y , refl , w })
                       (λ a → refl))) ⟩
  Σ (X (sequence S) 0) (λ x₀ → Σ ((n : ℕ) → X (sequence S) (suc n)) λ y → (π (sequence S) (y 0) ≡ x₀) × ((n : ℕ) → π (sequence S) (y (suc n)) ≡ y n))
    ≡⟨ (isoToPath (iso (λ {(a , (b , c)) -> M-combine-helper (X (sequence S)) a b , c})
                       (λ {(a , b) -> a 0 , (λ n → a (suc n)) , b})
                       (λ {(a , (b , c)) -> λ i → (λ n → M-combine-helper-lemma (X (sequence S)) a n i) , b , c})
                       (λ {(a , (b , c)) -> λ i → a , (b , c)}))) ⟩
  Σ ((n : ℕ) → X (sequence S) n) (λ x → (π (sequence S) (x 1) ≡ x 0) × ((n : ℕ) → π (sequence S) (x (suc (suc n))) ≡ x (suc n)))
    ≡⟨ (λ i -> Σ {ℓ} {ℓ} ((n : ℕ) → X (sequence S) n) λ x →
       isoToPath
           {A = (π (sequence S) (x 1) ≡ x 0) × ((n : ℕ) → π (sequence S) (x (suc (suc n))) ≡ x (suc n))}
           {B = (n : ℕ) → π (sequence S) (x (suc n)) ≡ x n}
         (iso (λ { (a , b) 0 → a ; (a , b) (suc n) → b n }) (λ x → x 0 , (λ n → x (suc n))) (λ { b i 0 → b 0 ; b i (suc n) → b (suc n) }) (λ { (a , b) i → a , b })) i) ⟩
  L (sequence S) ∎

M : ∀ {ℓ} -> Container {ℓ} → Set ℓ
M = L ∘ sequence

PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
PX,Pπ {ℓ} S =
  (λ n → P₀ {S = S} (X (sequence S) n)) ,,
  (λ {n : ℕ} x → P₁ (λ z → z) (π (sequence S) {n = suc n} x ))

swap-Σ-∀ :
  ∀ {ℓ} (X : ℕ -> Set ℓ)
    -> (A : Set ℓ)
    -> (B : A -> Set ℓ)
    -> (p : {n : ℕ} -> Σ A (λ a -> B a -> X (suc n)) -> Σ A (λ a -> B a -> X n) -> Set ℓ)
    -> (Σ (∀ (n : ℕ) -> Σ A (λ a -> B a -> X n)) (λ w -> (n : ℕ) -> p (w (suc n)) (w n)))
    -----------------------
    ≡ (Σ ((n : ℕ) → A) λ a → Σ ((n : ℕ) → B (a n) → X n) λ u → (n : ℕ) -> p (a (suc n) , u (suc n)) (a n , u n))
swap-Σ-∀ X A B p = isoToPath (iso (λ {(x , y) → (λ n → x n .fst) , (λ n → x n .snd) , y})
                                   (λ {(x , (y , z)) → (λ n → (x n) , y n) , z})
                                   (λ b → refl)
                                   (λ a → refl))

projection : ∀ {ℓ} {S : Container {ℓ}} n -> M S -> X (sequence S) n
projection n (x , q) = x n

β : ∀ {ℓ} {S : Container {ℓ}} -> (n : ℕ) → ∀ x → π (sequence S) {n = n} (projection (suc n) x) ≡ projection n x
β n (x , q) = q n

lemma10 : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ .fst -> M S) ≡ Cone C,γ
lemma10 {S = S} C,γ@(C , γ) =
  isoToPath (iso (λ {f → (λ n z → projection n (f z)) , λ n i a → β n (f a) i})
                 (λ {(u , q) z → (λ n → u n z) , (λ n i → q n i z)})
                 (λ _ → refl)
                  λ _ → refl)

postulate
  lemma11-helper-0 : ∀ {ℓ} {S : Container {ℓ}} (ρ : (n : ℕ) -> X (sequence S) n -> X (sequence S) (suc n)) x n -> (π (sequence S) (transport (λ _ → (n₁ : ℕ) → X (sequence S) n₁) x (suc n)) ≡ transport (λ _ → (n₁ : ℕ) → X (sequence S) n₁) x n) ≡ (ρ (transport (sym (λ _ → ℕ)) n) (x (transport (sym (λ _ → ℕ)) n)) ≡ x (suc (transport (sym (λ _ → ℕ)) n)))

  lemma11-helper-1 : ∀ {ℓ} {S : Container {ℓ}} (ρ : (n : ℕ) -> X (sequence S) n -> X (sequence S) (suc n)) x -> Σ (Lift {ℓ-zero} {ℓ} Unit) (λ _ → (n : ℕ) → ρ n (x n) ≡ x (suc n)) ≡ ((n : ℕ) → ρ n (transport (λ _ → (n₁ : ℕ) → X (sequence S) n₁) x n) ≡ transport (λ _ → (n₁ : ℕ) → X (sequence S) n₁) x (suc n))

  lemma11-helper-2 : ∀ {ℓ} {S : Container {ℓ}} (ρ : (n : ℕ) -> X (sequence S) n -> X (sequence S) (suc n)) -> Σ ((n : ℕ) → X (sequence S) n) (λ x → Σ (Lift {ℓ-zero} {ℓ} Unit) (λ _ → (n : ℕ) → ρ n (x n) ≡ x (suc n))) ≡ X (sequence S) 0

lemma11-helper : ∀ {ℓ} {S : Container {ℓ}} (ρ : (n : ℕ) -> X (sequence S) n -> X (sequence S) (suc n)) -> M S ≡ X (sequence S) 0
lemma11-helper {ℓ} {S = S} ρ =
    M S
  ≡⟨ sym (Σ-ap-iso refl (λ x → Π-ap-iso refl λ n → sym (lemma11-helper-0 ρ x n))) ⟩
    Σ ((n : ℕ) → X (sequence S) n) (λ x → ∀ n → ρ n (x n) ≡ x (suc n))
  ≡⟨ sym (Σ-ap-iso refl λ x → lemma11-helper-1 ρ x) ⟩
    Σ ((n : ℕ) → X (sequence S) n) (λ x → Σ (Lift {ℓ-zero} {ℓ} Unit) λ _ -> ∀ n → ρ n (x n) ≡ x (suc n))
  ≡⟨ lemma11-helper-2 ρ ⟩
    X (sequence S) 0 ∎

postulate
  lemma11 : ∀ {ℓ} {S : Container {ℓ}} -> M S ≡ X (sequence S) 0
  lemma11' : ∀ {ℓ} {S : Container {ℓ}} → S .fst ≡ Σ (ℕ → S .fst) (λ a → (n : ℕ) → a (suc n) ≡ a n)

postulate
  reduced-todo :
    ∀ {ℓ} (S : Container {ℓ}) ->
    Σ (Σ (ℕ → S .fst) λ a → (n : ℕ) → a (suc n) ≡ a n) (λ {(a , q) → Σ ((n : ℕ) → (b : S .snd (a n)) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → S .snd (q n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n)})
      ≡
    Σ (S .fst) (λ a → Σ ((n : ℕ) → S .snd a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
α-iso {S = S@(A , B)} =
  L (PX,Pπ S)
    ≡⟨ (swap-Σ-∀ (X (sequence S)) (S .fst) (S .snd) λ {n} a b → (P₁ (π (sequence S) {n = n})) a ≡ b) ⟩
  Σ ((n : ℕ) → A) (λ a → Σ ((n : ℕ) → B (a n) → X (sequence S) n) λ u → (n : ℕ) → P₁ {S = S} (π (sequence S) {n = n}) (a (suc n) , u (suc n)) ≡ (a n , u n))
    ≡⟨ Σ-ap-iso₂ (λ a → Σ-ap-iso₂ λ u → refl) ⟩
  Σ ((n : ℕ) → A) (λ a → Σ ((n : ℕ) → B (a n) → X (sequence S) n) λ u → (n : ℕ) → (a (suc n) , π (sequence S) {n = n} ∘ (u (suc n))) ≡ (a n , u n))
    ≡⟨ Σ-ap-iso₂ (λ a → isoToPath (iso (λ {(a , b) → (λ n i → b n i .fst) , a , (λ n x → b n x .snd)})
                                         (λ {(a , (b , c)) → b , λ n i → a n i , c n i})
                                         (λ {(a , b) → refl})
                                         (λ {(a , b) → refl}))) ⟩
  Σ ((n : ℕ) → A) (λ a → Σ ((n : ℕ) → a (suc n) ≡ a n) λ p → Σ ((n : ℕ) → B (a n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (p n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
    ≡⟨ isoToPath (iso (λ {(a , b , c , d) → (a , b) , (c , d)}) (λ {((a , b) , (c , d)) → a , (b , (c , d))}) (λ b → refl) λ a → refl) ⟩
  Σ (Σ (ℕ → A) λ a → (n : ℕ) → a (suc n) ≡ a n) (λ {(a , q) → Σ ((n : ℕ) → (b : B (a n)) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (q n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n)})
    ≡⟨ reduced-todo S ⟩
  Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
    ≡⟨ Σ-ap-iso₂ (λ a → sym (lemma10 (B a , (λ x → a , λ x₁ → x₁)))) ⟩ -- x₁ or x , are they equal ?
  Σ A (λ a → B a → M S)
    ≡⟨ refl ⟩
  P₀ {S = S} (M S) ∎

-----------------------------------------------------
-- Shifting the limit of a chain is an equivalence --
-----------------------------------------------------

-- P commutes with limits
shift : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M S) ≡ M S
shift {S = S} = 
  (sym α-iso) □ (L-unique {S = S}) -- lemma 13 & lemma 12

-- Transporting along shift

in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M S) -> M S
in-fun {S = S} = transport (shift {S = S})

out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M S -> P₀ (M S)
out-fun {S = S} = transport (sym (shift {S = S}))
