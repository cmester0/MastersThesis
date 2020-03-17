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

open import Cubical.Data.Sum

open import helper
open import Container

open import Coalg.Base

module M.Base where
--------------------------------
-- Limit of a Chain is Unique --
--------------------------------

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

PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
PX,Pπ {ℓ} S =
  (λ n → P₀ {S = S} (X (sequence S) n)) ,,
  (λ {n : ℕ} x → P₁ (λ z → z) (π (sequence S) {n = suc n} x ))

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

helper-todo :
    ∀ {ℓ} (S : Container {ℓ}) ->
    (b : Σ (ℕ → S .fst) (λ v → (n₁ : ℕ) → v (suc n₁) ≡ v n₁))
    (n : ℕ) → (b .fst 0) ≡ (b .fst n)
helper-todo S b 0 = refl
helper-todo S b (suc n) i = compPath-filler (helper-todo S b n) (sym (b .snd n)) i1 i

-- postulate -- something wtih lemma 11
reduced-todo' :
  ∀ {ℓ} (S : Container {ℓ}) ->
    (S .fst) ≡ (Σ (ℕ → S .fst) (λ a → (n : ℕ) → a (suc n) ≡ a n))
reduced-todo' S =
  let temp = lemma11 {S = S} {!!} in
    {!!}
  -- isoToPath (iso (λ x → (λ x₁ → x) , λ n → refl)
  --                (λ x → x .fst 0)
  --                (λ x → {!!})
  --                (λ a → refl))

-- λ i → (λ _ → x .fst {!!}) , λ n i₁ → x .snd {!!} i₁

postulate
  reduced-todo :
    ∀ {ℓ} (S : Container {ℓ}) ->
    forall x ->
    let (A , B) = S in
       Σ ((n : ℕ) → B x → X (sequence (A , B)) n) (λ u → (n : ℕ) → (λ x₁ → π (sequence (A , B)) (u (suc n) x₁)) ≡ u n)
    ≡ Σ ((n : ℕ) → B (transport (reduced-todo' (A , B)) x .fst n) → X (sequence (A , B)) n)
    (λ u → (n : ℕ) → PathP (λ x₁ → B (transport (reduced-todo' (A , B)) x .snd n x₁) → X (sequence (A , B)) n) (λ x₁ → π (sequence (A , B)) (u (suc n) x₁)) (u n))

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

postulate
  α-iso-step-5 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
    ≡ Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
-- α-iso-step-5 {S = S} =  
--   sym (Σ-ap-iso (reduced-todo' S) (reduced-todo S))

postulate
  α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
    ≡ Σ A (λ a → B a → M S)  
-- α-iso-step-6 {S = S@(A , B)}=
--   Σ-ap-iso₂ (λ a → sym (lemma10 (B a , (λ x → a , λ x₁ → x₁))))

postulate
  temp-post : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
    ≡ Σ A (λ a → B a → M S)  

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
α-iso {S = S@(A , B)} =
  α-iso-step-1-4 □ (α-iso-step-5 □ α-iso-step-6)
  -- (α-iso-step-4 □
  -- (α-iso-step-5 □
  -- α-iso-step-6))))
  
  -- L (PX,Pπ S)
  --   ≡⟨ α-iso-step-1 ⟩
  -- Σ ((n : ℕ) → A) (λ a → Σ ((n : ℕ) → B (a n) → X (sequence S) n) λ u → (n : ℕ) → P₁ {S = S} (π (sequence S) {n = n}) (a (suc n) , u (suc n)) ≡ (a n , u n))
  --   ≡⟨ α-iso-step-2 ⟩
  -- Σ ((n : ℕ) → A) (λ a → Σ ((n : ℕ) → B (a n) → X (sequence S) n) λ u → (n : ℕ) → (a (suc n) , π (sequence S) {n = n} ∘ (u (suc n))) ≡ (a n , u n))
  --   ≡⟨ α-iso-step-3 ⟩
  -- Σ ((n : ℕ) → A) (λ a → Σ ((n : ℕ) → a (suc n) ≡ a n) λ p → Σ ((n : ℕ) → B (a n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (p n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
  --   ≡⟨ α-iso-step-4 ⟩ -- aa 
  -- (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
  --   ≡⟨ α-iso-step-5 ⟩
  -- Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
  --   ≡⟨ α-iso-step-6 ⟩ -- x₁ or x , are they equal ?
  -- Σ A (λ a → B a → M S)
  --   ≡⟨ refl ⟩
  -- P₀ {S = S} (M S) ∎

-----------------------------------------------------
-- Shifting the limit of a chain is an equivalence --
-----------------------------------------------------

postulate
  α-iso' : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
  L-unique' : ∀ {ℓ} -> {S : Container {ℓ}} -> L (shift-chain (sequence S)) ≡ L (sequence S)
  
-- P commutes with limits
-- postulate -- TODO: Slow computations..
shift : ∀ {ℓ} {S : Container {ℓ}} -> P₀ {S = S} (M S) ≡ M S
shift {S = S} = 
  (sym α-iso) □ (L-unique' {S = S}) -- lemma 13 & lemma 12

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
