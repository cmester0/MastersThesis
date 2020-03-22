{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma

open import Cubical.Foundations.Transport

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sum

open import helper
open import Container

open import Coalg.Base

module M.Base where
--------------------------------
-- Limit of a Chain is Unique --
--------------------------------

-- Lemma 12
L-unique : ∀ {ℓ} -> {S : Container {ℓ}} -> L (shift-chain (sequence S)) ≡ L (sequence S)
L-unique {ℓ} {S = S} =
  isoToPath (
    iso (λ x → (λ {0 → lift tt ; (suc n) -> x .fst n}) , (λ { 0 → refl {x = lift tt} ; (suc n) → x .snd n }))
        (λ x → x .fst ∘ suc , x .snd ∘ suc)
        (λ {(b , c) → ΣPathP (funExt (λ { 0 → refl ; (suc n) → refl }) , λ {i 0 → refl ; i (suc n) → c (suc n)})})
        (λ a → ΣPathP (refl , refl)))

PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
PX,Pπ {ℓ} S =
  (λ n → P₀ {S = S} (X (sequence S) n)) ,,
  (λ {n : ℕ} x → P₁ (λ z → z) (π (sequence S) {n = suc n} x ))

--------------
-- Lemma 10 --
--------------

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

------------------------------------
-- Shifting M-type is an equality --
------------------------------------

swap-Σ-∀ :
  ∀ {ℓ} (X : ℕ -> Set ℓ)
    -> (A : Set ℓ)
    -> (B : A -> Set ℓ)
    -> (p : {n : ℕ} -> Σ A (λ a -> B a -> X (suc n)) -> Σ A (λ a -> B a -> X n) -> Set ℓ)
    -----------------------
    -> (Σ (∀ (n : ℕ) -> Σ A (λ a -> B a -> X n)) (λ w -> (n : ℕ) -> p (w (suc n)) (w n)))
    ≡ (Σ ((n : ℕ) → A) λ a → Σ ((n : ℕ) → B (a n) → X n) λ u → (n : ℕ) -> p (a (suc n) , u (suc n)) (a n , u n))
swap-Σ-∀ X A B p = isoToPath (iso (λ {(x , y) → (λ n → x n .fst) , (λ n → x n .snd) , y})
                                   (λ {(x , (y , z)) → (λ n → (x n) , y n) , z})
                                   (λ b → refl)
                                   (λ a → refl))

contr-⊤-iso : ∀ {i}{X : Set i} → isContr X → X ≡ Lift Unit
contr-⊤-iso hX = isoToPath (iso (λ _ → lift tt)
                                (λ _ → fst hX)
                                (λ {(lift tt) → refl})
                                λ a → snd hX a)

lemma11-helper : ∀ {ℓ} {S : Container {ℓ}} -> (χ : (x₀ : X (sequence S) 0)
              → isContr ( Σ ((n : ℕ) → X (sequence S) n) λ x
              → (x₀ ≡ x 0)
              × (∀ n → π (sequence S) (x (suc n)) ≡ x n) ) )  → M S ≡ X (sequence S) 0
lemma11-helper {ℓ} {S = S} χ =
  M S
    ≡⟨ sym (Σ-ap-iso₂ λ x → ∏-ap-iso refl λ n → refl) ⟩ -- sym not needed
  Σ ((n : ℕ) → X (sequence S) n) (λ x → (n : ℕ) → π (sequence S) (x (suc n)) ≡ x n)
    ≡⟨ sym (Σ-ap-iso₂ λ x → isoToPath (iso (λ x₁ → x₁ .snd) (λ x₁ → lift tt , x₁) (λ b → refl) λ a → refl)) ⟩
  Σ ((n : ℕ) → X (sequence S) n) (λ x → Σ (Lift Unit) λ _ → (n : ℕ) → π (sequence S) (x (suc n)) ≡ x n)
    ≡⟨ Σ-ap-iso₂ (λ x →
       Σ-ap-iso (isoToPath (iso (λ x₁ → (lift tt) , (λ i → lift tt)) (λ x₁ → lift tt) (λ {(a , b) → λ _ → (lift tt) , (λ _ → lift tt)}) λ a → refl)) λ _ → refl) ⟩
  Σ ((n : ℕ) → X (sequence S) n) (λ x →
  Σ (singl (x 0)) λ _ → (n : ℕ) → π (sequence S) (x (suc n)) ≡ x n)
    ≡⟨ isoToPath (iso (λ {(x , (z , p) , q) → z , x , p , q})
                      (λ {(lift tt , x , p , q) → x , ((lift tt) , p) , q})
                      (λ {(lift tt , x , p , q) → refl})
                      (λ {(x , (lift tt , p) , q) → refl})) ⟩
  Σ (X (sequence S) 0) (λ z →
  Σ ((n : ℕ) → X (sequence S) n) λ x →
  Σ (z ≡ x 0) λ _ →
    (n : ℕ) → π (sequence S) (x (suc n)) ≡ x n)
    ≡⟨ (Σ-ap-iso₂ λ z → let temp = χ z in contr-⊤-iso ((temp .fst .fst , proj₁ (temp .fst .snd) , proj₂ (temp .fst .snd)) , λ y → λ i → let temp' = temp .snd ((y .fst) , (y .snd .fst) , (y .snd .snd)) in (temp' i .fst) , proj₁ (temp' i .snd) , proj₂ (temp' i .snd))) ⟩
  (Σ (X (sequence S) 0) λ z → Lift Unit)
    ≡⟨ isoToPath (iso (λ _ → lift tt) (λ _ → lift tt , lift tt) (λ b → refl) λ a → refl) ⟩
  X (sequence S) 0 ∎

postulate
  lemma11 : ∀ {ℓ} {S : Container {ℓ}} -> M S ≡ X (sequence S) 0

α-iso-step-1-4 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    L (PX,Pπ S)
    ≡ (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
α-iso-step-1-4 {S = S@(A , B)} =
  isoToPath (iso
    (λ a →
      ((λ n → a .fst n .fst) , (λ n i → a .snd n i .fst)) ,
      ((λ n → a .fst n .snd) , (λ n x₁ → a .snd n x₁ .snd)))
    (λ a →
      (λ n → (a .fst .fst n) , (a .snd .fst n)) ,
      (λ n i → a .fst .snd n i , a .snd .snd n i))
    (λ b → refl)
    (λ a → refl))

helper-todo :
    ∀ {ℓ} (A : Set ℓ) ->
    (b : Σ (ℕ → A) (λ v → (n₁ : ℕ) → v (suc n₁) ≡ v n₁))
    (n : ℕ) → (b .fst n) ≡ (b .fst 0)
helper-todo A b 0 = refl
helper-todo A b (suc n) = (b .snd n) □ (helper-todo A b n)

postulate
  close-loop : ∀ {ℓ} {A : Set ℓ} {x y : A} {a : x ≡ y} →
    transport (λ i → a i  ≡ a i1) a ≡ refl {x = y}

-- helper-todo-2-helper-helper :  ∀ {ℓ} (A : Set ℓ)
--   → (b : Σ (ℕ → A) (λ v → (n₁ : ℕ) → v (suc n₁) ≡ v n₁))
--   -> (n : ℕ)
--   -> (transport (λ i → ((b .snd (suc n)) □ (b .snd n)) i
--                     ≡ (b .snd n) i)
--                 (snd b (suc n)))
--   ≡ (transport (λ i → (b .snd n) i
--                      ≡ refl {x = b .fst n} i)
--                 (snd b n))
-- helper-todo-2-helper-helper = {!!}

postulate
  helper-todo-2-helper : ∀ {ℓ} (A : Set ℓ)
    → (b : Σ (ℕ → A) (λ v → (n₁ : ℕ) → v (suc n₁) ≡ v n₁))
    -------------------------
    → ∀ (n : ℕ)
    → transport (λ i → (n₁ : ℕ) →
              funExt (helper-todo A b) i (suc n₁) ≡
              funExt (helper-todo A b) i n₁) (snd b) n
    ≡ refl
-- helper-todo-2-helper A b ℕ.zero =
--   transport (λ i → (n₁ : ℕ) → funExt (helper-todo A b) i (suc n₁) ≡ funExt (helper-todo A b) i n₁) (snd b) ℕ.zero
--     ≡⟨ refl ⟩
--   transport (λ i → funExt (helper-todo A b) i (suc 0) ≡ funExt (helper-todo A b) i 0) (snd b 0)
--     ≡⟨ refl ⟩
--   transport (λ i → helper-todo A b (suc 0) i  ≡ helper-todo A b 0 i) (snd b 0)
--     ≡⟨ refl ⟩
--   transport (λ i → ((b .snd 0) □ (helper-todo A b 0)) i  ≡ (helper-todo A b 0) i) (snd b 0)
--     ≡⟨ refl ⟩
--   transport (λ i → (b .snd 0 □ refl) i  ≡ refl i) (snd b 0)
--     ≡⟨ cong (λ a → transport (λ i → a i ≡ refl {x = b .fst 0} i) (snd b 0)) (□≡∙ (b .snd 0) refl) ⟩
--   transport (λ i → (b .snd 0 ∙ refl {x = b .fst 0}) i  ≡ refl {x = b .fst 0} i) (snd b 0)
--     ≡⟨ cong (λ a → transport (λ i → a i ≡ refl {x = b .fst 0} i) (snd b 0)) (sym (rUnit (b .snd 0))) ⟩
--   transport (λ i → (b .snd 0) i  ≡ refl {x = b .fst 0} i) (snd b 0)
--     ≡⟨ refl ⟩
--   transport (λ i → b .snd 0 i  ≡ b .snd 0 i1) (snd b 0)
--     ≡⟨ close-loop ⟩
--   (λ _ → b .snd 0 i1)
--     ≡⟨ refl ⟩
--   (λ _ → b .fst 0)
--     ≡⟨ refl ⟩
--   refl ∎

-- helper-todo-2-helper A b (suc n) =
--   let temp : ∀ {ℓ} {X : Set ℓ} {Y : Set ℓ} {Z : Set ℓ} {W : Set ℓ}
--            → ∀ (a : (X ≡ Y) ≡ (Z ≡ W)) c b x
--            → transport (λ i → (a □ b) i ≡ (c □ b) i) x
--            ≡ transport (λ i → b i ≡ b i) (transport (λ i → a i ≡ c i) x)
--       temp = {!!}
--   in
--   let temp' : ∀ (nn : ℕ)
--             (vv : (ℕ → A))
--             (pp : (n : ℕ) → vv (suc n) ≡ vv n)
--             (aa : vv (suc (suc nn)) ≡ vv nn)
--             (cc : vv (suc nn) ≡ vv nn)
--             (bb : vv nn ≡ vv 0)
--             (x : ((pp (suc nn) □ cc) □ bb) i0 ≡ (cc □ bb) i0)
--            -> transport (λ i → (aa □ bb) i ≡ (cc □ bb) i) x
--            ≡ transport (λ i → bb i ≡ bb i) (transport (λ i → aa i ≡ cc i) x)
--       temp' nn vv pp aa cc bb x = {!!}
--   in
--   let temp'' : {!!}
--       temp'' = (b .snd (suc n))
--   in
--   transport (λ i → (n₁ : ℕ) → funExt (helper-todo A b) i (suc n₁)
--                               ≡ funExt (helper-todo A b) i n₁)
--             (b .snd) (suc n)
--     ≡⟨ refl ⟩
--   transport (λ i → funExt (helper-todo A b) i (suc (suc n))
--                  ≡ funExt (helper-todo A b) i (suc n))
--             (b .snd (suc n))
--     ≡⟨ refl ⟩
--   transport (λ i → helper-todo A b (suc (suc n)) i
--                  ≡ helper-todo A b (suc n) i)
--             (b .snd (suc n))
--     ≡⟨ refl ⟩
--   transport (λ i → ((b .snd (suc n)) □ (helper-todo A b (suc n))) i
--                  ≡ (helper-todo A b (suc n)) i)
--             (b .snd (suc n))
--     ≡⟨ refl ⟩
--   transport (λ i → ((b .snd (suc n)) □ ((b .snd n) □ helper-todo A b n)) i
--                  ≡ ((b .snd n) □ helper-todo A b n) i)
--             (b .snd (suc n))
--     ≡⟨ cong (λ a → transport (λ i → ((b .snd (suc n)) □ a) i ≡ (b .snd n □ helper-todo A b n) i) (snd b (suc n))) (□≡∙ (b .snd n) (helper-todo A b n)) ⟩
--   transport (λ i → ((b .snd (suc n)) □ ((b .snd n) ∙ helper-todo A b n)) i
--                  ≡ ((b .snd n) □ helper-todo A b n) i)
--             (b .snd (suc n))
--     ≡⟨ cong (λ a → transport (λ i → a i ≡ (b .snd n □ helper-todo A b n) i) (snd b (suc n))) (□≡∙ (b .snd (suc n)) (b .snd n ∙ helper-todo A b n)) ⟩
--   transport (λ i → ((b .snd (suc n)) ∙ (b .snd n) ∙ helper-todo A b n) i
--                  ≡ ((b .snd n) □ helper-todo A b n) i)
--             (b .snd (suc n))
--     ≡⟨ cong (λ a → transport (λ i → a i ≡ (b .snd n □ helper-todo A b n) i) (snd b (suc n))) (assoc (b .snd (suc n)) (b .snd n) (helper-todo A b n)) ⟩
--   transport (λ i → (((b .snd (suc n)) ∙ (b .snd n)) ∙ helper-todo A b n) i
--                  ≡ ((b .snd n) □ helper-todo A b n) i)
--             (b .snd (suc n))
--     ≡⟨ cong (λ a → transport (λ i → (a ∙ helper-todo A b n) i ≡ (b .snd n □ helper-todo A b n) i) (snd b (suc n))) (sym (□≡∙ (b .snd (suc n)) (b .snd n))) ⟩
--   transport (λ i → (((b .snd (suc n)) □ (b .snd n)) ∙ helper-todo A b n) i
--                  ≡ ((b .snd n) □ helper-todo A b n) i)
--             (b .snd (suc n))
--     ≡⟨ cong (λ a → transport (λ i → a i ≡ (b .snd n □ helper-todo A b n) i) (snd b (suc n))) (sym (□≡∙ (b .snd (suc n) □ b .snd n) (helper-todo A b n))) ⟩
--   transport (λ i → (((b .snd (suc n)) □ (b .snd n)) □ helper-todo A b n) i
--                  ≡ ((b .snd n) □ helper-todo A b n) i)
--             (b .snd (suc n))
--     ≡⟨ temp' n (b .fst) (b .snd) (b .snd (suc n) □ b .snd n) (b .snd n) (helper-todo A b n) (snd b (suc n)) ⟩
--   transport (\ i -> helper-todo A b n i ≡ helper-todo A b n i)
--     (transport (λ i → ((b .snd (suc n)) □ (b .snd n)) i
--                     ≡ (b .snd n) i)
--                (b .snd (suc n)))
--     ≡⟨ cong (transport (λ i → helper-todo A b n i ≡ helper-todo A b n i)) {!!} ⟩
--   transport (λ i → helper-todo A b n i ≡ helper-todo A b n i)
--     (transport (λ i → (b .snd n) i
--                     ≡ refl {x = b .fst n} i)
--                (b .snd n))
--             ≡⟨ {!!} ⟩
--   transport (λ i → ((b .snd n) □ helper-todo A b n) i
--                  ≡ (helper-todo A b n) i) (b .snd n)
--     ≡⟨ helper-todo-2-helper A b n ⟩
--   refl ∎

helper-todo-2 :
  ∀ {ℓ} (A : Set ℓ)
  → (b : Σ (ℕ → A) (λ v → (n₁ : ℕ) → v (suc n₁) ≡ v n₁))
  → ((λ _ → b .fst 0) , (λ _ → refl)) ≡ b
helper-todo-2 A b = sym (sigmaPath→pathSigma b ((λ _ → b .fst 0) , (λ _ → refl)) (funExt (helper-todo A b) , funExt (helper-todo-2-helper A b)))

-- λ {0 →
--   transport (λ i → (n₁ : ℕ) → funExt (helper-todo A b) i (suc n₁) ≡ funExt (helper-todo A b) i n₁) (snd b) 0
--     ≡⟨ refl ⟩
--   transport (λ i → funExt (helper-todo A b) i (suc 0) ≡ funExt (helper-todo A b) i 0) (snd b 0)
--     ≡⟨ refl ⟩
--   transport (λ i → helper-todo A b (suc 0) i  ≡ helper-todo A b 0 i) (snd b 0)
--     ≡⟨ refl ⟩
--   transport (λ i → ((b .snd 0) □ (helper-todo A b 0)) i  ≡ (helper-todo A b 0) i) (snd b 0)
--     ≡⟨ refl ⟩
--   transport (λ i → (b .snd 0 □ refl) i  ≡ refl i) (snd b 0)
--     ≡⟨ cong (λ a → transport (λ i → a i ≡ refl {x = b .fst 0} i) (snd b 0)) (□≡∙ (b .snd 0) refl) ⟩
--   transport (λ i → (b .snd 0 ∙ refl {x = b .fst 0}) i  ≡ refl {x = b .fst 0} i) (snd b 0)
--     ≡⟨ cong (λ a → transport (λ i → a i ≡ refl {x = b .fst 0} i) (snd b 0)) (sym (rUnit (b .snd 0))) ⟩
--   transport (λ i → (b .snd 0) i  ≡ refl {x = b .fst 0} i) (snd b 0)
--     ≡⟨ refl ⟩
--   transport (λ i → b .snd 0 i  ≡ b .snd 0 i1) (snd b 0)
--     ≡⟨ close-loop ⟩
--   (λ _ → b .snd 0 i1)
--     ≡⟨ refl ⟩
--   (λ _ → b .fst 0)
--     ≡⟨ refl ⟩
--   refl ∎}

  --   ≡⟨ (cong (λ a → transport (λ i → a i ≡ (b .fst 0)) (snd b 0)) {!!}) ⟩
  -- transport (λ i → (b .snd 0) i  ≡ (b .fst 0)) (snd b 0)


  -- transport (λ i → (n₁ : ℕ) → funExt (helper-todo A b) i (suc n₁) ≡ funExt (helper-todo A b) i n₁) (snd b) n
  --   ≡⟨ refl ⟩
  -- transport (λ i → funExt (helper-todo A b) i (suc n) ≡ funExt (helper-todo A b) i n) (snd b n)
  --   ≡⟨ refl ⟩
  -- transport (λ i → helper-todo A b (suc n) i  ≡ helper-todo A b n i) (snd b n)
  --   ≡⟨ refl ⟩
  -- transport (λ i → ((b .snd n) □ (helper-todo A b n)) i  ≡ (helper-todo A b n) i) (snd b n)
  --   ≡⟨ cong (λ a → transport (λ i → a i ≡ helper-todo A b n i) (snd b n)) (□≡∙ (b .snd n) (helper-todo A b n)) ⟩
  -- transport (λ i → ((b .snd n) ∙ (helper-todo A b n)) i  ≡ (helper-todo A b n) i) (snd b n)
  --   ≡⟨ cong (λ a → transport (λ i → (b .snd n ∙ helper-todo A b n) i ≡ a i) (snd b n)) (lUnit (helper-todo A b n)) ⟩
  -- transport (λ i → ((b .snd n) ∙ (helper-todo A b n)) i  ≡ (refl ∙ helper-todo A b n) i) (snd b n)
  --   ≡⟨ refl ⟩
  -- transp (λ i → ((b .snd n) ∙ (helper-todo A b n)) i  ≡ (refl ∙ helper-todo A b n) i) i0 (snd b n)
  --   ≡⟨ {!!} ⟩
  -- (refl ∙ helper-todo A b n)
  --   ≡⟨ {!!} ⟩
  -- refl ∎))

  --   ≡⟨ refl ⟩
  -- transp (λ i → helper-todo A b (suc n) i  ≡ helper-todo A b n i) i0 (snd b n)
  --   ≡⟨ refl ⟩
  -- transp (λ i → ((b .snd n) □ (helper-todo A b n)) i  ≡ helper-todo A b n i) i0 (snd b n)


  -- (λ _ → helper-todo A b (suc n) i1)
  --   ≡⟨ refl ⟩
  -- (λ _ → helper-todo A b n i1)
  --   ≡⟨ refl ⟩
  -- (λ _ → helper-todo A b 1 i1)
  --   ≡⟨ refl ⟩
  -- (λ _ → snd b 0 i1)
  --   ≡⟨ refl ⟩
  -- (λ _ → b .fst 0)
  --   ≡⟨ refl ⟩


-- transport (λ i → helper-todo A b (suc x) i  ≡ helper-todo A b x i) (snd b x)

-- {!!} ≡⟨ {!!} ⟩ {!!} ∎

  -- (λ n → b .fst 0) , (λ n → refl)
  --   ≡⟨ (λ i → (λ n → helper-todo A b n (~ i)) , λ n → {!!}) ⟩
  -- (λ n → b .fst n) , (λ n i → b .snd n i)
  --   ≡⟨ refl ⟩
  -- b .fst , b .snd
  --   ≡⟨ refl ⟩
  -- b ∎

  -- let temp : isContr (ℕ → A)
  --     temp = {!!}
  -- in
  -- transport Σ-split-iso (funExt (λ {0 → sym (helper-todo A b 0) ; (suc n) → sym (helper-todo A b (suc n))})
  -- , λ {i 0 → {!!} ; i (suc n) i₁ → {!!}})

-- transport Σ-split-iso (funExt (λ x → sym (helper-todo A b x)) , {!!})


postulate -- something with lemma 11
  -- helper-todo-2 :
  --   ∀ {ℓ} (A : Set ℓ)
  --   → (b : Σ (ℕ → A) (λ v → (n₁ : ℕ) → v (suc n₁) ≡ v n₁))
  --   → ((λ n → b .fst 0) , (λ n i → b .fst 0)) ≡ b
-- helper-todo-2 A b = transport Σ-split-iso (funExt (λ x → sym (helper-todo A b x)) , λ {i 0 → {!!}})

  helper-todo-3 :
    ∀ {ℓ} (A : Set ℓ) (B : A → Set ℓ) ->
    ∀ x
    → Σ ((n : ℕ) → B (x .fst n) → X (sequence (A , B)) n) (λ u → (n : ℕ) → PathP (λ x₁ → B (x .snd n x₁) → X (sequence (A , B)) n) ((λ {a} → π (sequence (A , B))) ∘ u (suc n)) (u n))
    ≡ Σ ((n : ℕ) → B (transport (isoToPath (iso (λ x₁ → x₁ .fst 0) (λ x₁ → (λ n₁ → x₁) , (λ n₁ i → x₁)) (λ b _ → b) (λ x₁ → helper-todo-2 A x₁))) x)
    → X (sequence (A , B)) n) (λ u → (n : ℕ) → (λ {a} → π (sequence (A , B))) ∘ u (suc n) ≡ u n)

α-iso-step-5 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
    ≡ Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
α-iso-step-5 {S = S@(A , B)} =
  let temp : Σ (ℕ → A) (λ v → (n₁ : ℕ) → v (suc n₁) ≡ v n₁) ≡ A
      temp = isoToPath (iso (λ x → x .fst 0)
                            (λ x → (λ n → x) , λ n i → x)
                            (λ b → refl)
                            (λ x → helper-todo-2 A x ))
  in
    Σ-ap-iso temp (helper-todo-3 A B)

α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
    ≡ Σ A (λ a → B a → M S)
α-iso-step-6 {S = S@(A , B)} = Σ-ap-iso₂ (λ a i → lemma10 (B a , (λ x → a , (λ x₁ → x₁))) (~ i))

-- TODO: Slow computations..
postulate
  α-iso' : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
α-iso {S = S@(A , B)} =
  α-iso-step-1-4 □ (α-iso-step-5 □ α-iso-step-6)

-----------------------------------------------------
-- Shifting the limit of a chain is an equivalence --
-----------------------------------------------------
  
shift : ∀ {ℓ} {S : Container {ℓ}} -> P₀ {S = S} (M S) ≡ M S
shift {S = S@(A , B)} = (sym α-iso') □ (L-unique {S = S}) -- lemma 13 & lemma 12

-- Transporting along shift

in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M S) -> M S
in-fun {S = S} = transport (shift {S = S})

out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M S -> P₀ (M S)
out-fun {S = S} = transport (sym (shift {S = S}))

----------------------------------------
-- Property of functions into M-types --
----------------------------------------

lift-to-M : ∀ {ℓ} {A : Set ℓ} {S : Container {ℓ}}
  → (x : (n : ℕ) -> A → X (sequence S) n)
  → ((n : ℕ) → (a : A) →  π (sequence S) (x (suc n) a) ≡ x n a)
  ---------------
  → (A → M S)
lift-to-M x p a = (λ n → x n a) , λ n i → p n a i

lift-direct-M : ∀ {ℓ} {S : Container {ℓ}}
  → (x : (n : ℕ) → X (sequence S) n)
  → ((n : ℕ) →  π (sequence S) (x (suc n)) ≡ x n)
  ---------------
  → M S
lift-direct-M x p = x , p
