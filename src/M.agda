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

module M where

-------------------------------------
-- Container and Container Functor --
-------------------------------------

Container : ∀ {ℓ} -> Set (ℓ-suc ℓ)
Container {ℓ} = Σ (Set ℓ) (λ A -> A -> Set ℓ)

P₀ : ∀ {ℓ} {S : Container {ℓ}} -> Set ℓ -> Set ℓ
P₀ {S = S} X  = Σ (S .fst) λ x → (S .snd x) -> X

P₁ : ∀ {ℓ} {S : Container {ℓ}} {X Y} (f : X -> Y) -> P₀ {S = S} X -> P₀ {S = S} Y
P₁ {S = S} f = λ { (a , g) ->  a , f ∘ g }

-----------------------
-- Chains and Limits --
-----------------------

record Chain {ℓ} : Set (ℓ-suc ℓ) where
  constructor _,,_
  field
    X : ℕ -> Set ℓ
    π : {n : ℕ} -> X (suc n) -> X n

open Chain

L : ∀ {ℓ} -> Chain {ℓ} → Set ℓ
L (x ,, pi) = Σ ((n : ℕ) → x n) λ x → (n : ℕ) → pi {n = n} (x (suc n)) ≡ x n

shift-chain : ∀ {ℓ} -> Chain {ℓ} -> Chain {ℓ}
shift-chain = λ X,π -> ((λ x → X X,π (suc x)) ,, λ {n} → π X,π {suc n})

-----------------------
-- Equivalence Rules --
-----------------------

M-combine-helper : ∀ {ℓ} (X : ℕ -> Set ℓ) ->
  X 0 -> ((n : ℕ) -> X (suc n)) -> (n : ℕ) -> X n
M-combine-helper X a b 0 = a
M-combine-helper X a b (suc n) = b n

M-combine-helper-lemma : ∀ {ℓ} (X : ℕ -> Set ℓ) (x : (n : ℕ) -> X n) n -> (M-combine-helper X (x 0) (λ (n : ℕ) -> x (suc n)) n) ≡ x n
M-combine-helper-lemma X x 0 = refl
M-combine-helper-lemma X x (suc n) = refl

M-combine :
  ∀ {ℓ} (X : ℕ -> Set ℓ) (p : ∀ {n} -> (X (suc n)) -> (X n) -> Set ℓ)
  ----------------------
  -> (Σ (X 0) λ x₀ → Σ ((n : ℕ) → X (suc n)) λ y → (p (y 0) x₀) × ((n : ℕ) → p (y (suc n)) (y n)))
  ≡ (Σ ((n : ℕ) → X n) λ x → (p (x 1) (x 0)) × ((n : ℕ) → p (x (suc (suc n))) (x (suc n))))
M-combine X p = isoToPath (iso (λ {(a , (b , c)) -> M-combine-helper X a b , c})
                               (λ {(a , b) -> a 0 , (λ n → a (suc n)) , b})
                               (λ {(a , (b , c)) -> λ i → (λ n → M-combine-helper-lemma X a n i) , b , c})
                               (λ {(a , (b , c)) -> λ i → a , (b , c)}))

M-intro-helper : ∀ {ℓ} -> {X,π : Chain {ℓ}} ->
  ∀ (x₀ : X X,π 0) (y : ((n : ℕ) → X X,π (suc n)))
  (helper : isContr (X X,π 0)) ->
  (π X,π (y 0)) ≡ x₀
M-intro-helper {X,π = X,π} x₀ y helper = λ i ->
  compPath-filler (sym (helper .snd (π X,π (y 0)))) (helper .snd x₀) i i

M-intro-helper-2 : ∀ {ℓ} -> {X,π : Chain {ℓ}} ->
  ∀ (x₀ : X X,π 0) (y : ((n : ℕ) → X X,π (suc n)))
  (helper : isContr (X X,π 0)) -> ∀ i -> (π X,π (y 0)) ≡ M-intro-helper {X,π = X,π} x₀ y helper i
M-intro-helper-2 {X,π = X,π} x₀ y helper i = λ j ->
  compPath-filler (sym (helper .snd (π X,π (y 0)))) (helper .snd (M-intro-helper {X,π = X,π} x₀ y helper i)) j j

postulate
  combine2 : ∀ {ℓ} (X : ℕ -> Set ℓ) -> (p : ∀ {n} -> (X (suc n)) -> (X n) -> Set ℓ) -> (y : (n : ℕ) -> X n) ->
    p (y 1) (y 0) × ((n : ℕ) → p (y (suc (suc n))) (y (suc n))) ≡ ((n : ℕ) → p (y (suc n)) (y n))

! : ∀ {ℓ} {A : Set ℓ} (x : A) -> Lift {ℓ-zero} {ℓ} Unit
! x = lift tt

------------------------------------------------------
-- Limit type of a Container , and Shift of a Limit --
------------------------------------------------------

W : ∀ {ℓ} -> Container {ℓ} -> ℕ -> Set ℓ -- (ℓ-max ℓ ℓ')
W S 0 = Lift Unit
W S (suc n) = P₀ {S = S} (W S n)

πₙ : ∀ {ℓ} -> (S : Container {ℓ}) -> {n : ℕ} -> W S (suc n) -> W S n
πₙ {ℓ} S {0} = ! {ℓ}
πₙ S {suc n} = P₁ (πₙ S {n})

sequence : ∀ {ℓ} -> Container {ℓ} -> Chain {ℓ}
X (sequence {ℓ} S) n = W {ℓ} S n
π (sequence {ℓ} S) {n} = πₙ {ℓ} S {n}

--------------------------------
-- Limit of a Chain is Unique --
--------------------------------

M-intro : ∀ {ℓ} -> {S : Container {ℓ}}
    -> ((Σ ((n : ℕ) → X (sequence S) (suc n)) λ a -> (n : ℕ) → π (sequence S) (a (suc n)) ≡ a n)
    ≡ (Σ (X (sequence S) 0) (λ b -> Σ ((n : ℕ) → X (sequence S) (suc n)) λ a -> (π (sequence S) (a 0) ≡ b) × ((n : ℕ) → π (sequence S) (a (suc n)) ≡ a n))))
M-intro {S = S} =
  isoToPath (iso (λ {(x , y) → π (sequence S) (x 0) , x , refl , y})
                 (λ x → x .snd .fst , proj₂ (x .snd .snd))
                 (λ {(x , y , z , w)  → λ i → x , y , refl , w })
                 (λ a → refl))

-- Lemma 12
L-unique : ∀ {ℓ} -> {S : Container {ℓ}} -> L (shift-chain (sequence S)) ≡ L (sequence S)
L-unique {S = S} =
  L (shift-chain (sequence S))
    ≡⟨ (M-intro {S = S}) ⟩
  Σ (X (sequence S) 0) (λ x₀ → Σ ((n : ℕ) → X (sequence S) (suc n)) λ y → (π (sequence S) (y 0) ≡ x₀) × ((n : ℕ) → π (sequence S) (y (suc n)) ≡ y n))
    ≡⟨ (M-combine (X (sequence S)) λ a b -> π (sequence S) a ≡ b) ⟩
  Σ ((n : ℕ) → X (sequence S) n) (λ x → (π (sequence S) (x 1) ≡ x 0) × ((n : ℕ) → π (sequence S) (x (suc (suc n))) ≡ x (suc n)))
    ≡⟨ (λ i → Σ ((n : ℕ) → X (sequence S) n) λ x → combine2 (X (sequence S)) (λ a b → π (sequence S) a ≡ b) x i) ⟩
  L (sequence S) ∎

-- -- Lemma 12
-- L-unique : ∀ {ℓ} -> {X,π : Chain {ℓ}} -> L (shift-chain X,π) ≡ L X,π
-- L-unique {X,π = X,π} =
--   L (shift-chain X,π)
--     ≡⟨ (M-intro {X,π = X,π}) ⟩
--            -- (λ y → (n : ℕ) → π X,π (y (suc n)) ≡ y n)
--            -- (λ y x₀ → π X,π (y 0) ≡ x₀))
--            -- (λ y -> π X,π (y 0) , refl)
--   Σ (X X,π 0) (λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n))
--     ≡⟨ (M-combine (X X,π) λ a b -> π X,π a ≡ b) ⟩
--   Σ ((n : ℕ) → X X,π n) (λ x → (π X,π (x 1) ≡ x 0) × ((n : ℕ) → π X,π (x (suc (suc n))) ≡ x (suc n)))
--     ≡⟨ (λ i → Σ ((n : ℕ) → X X,π n) λ x → combine2 (X X,π) (λ a b → π X,π a ≡ b) x i) ⟩
--   L X,π ∎

-- -- M : ∀ {ℓ} -> Container {ℓ} → Set ℓ
-- -- M = L ∘ sequence

-- -- PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
-- -- PX,Pπ {ℓ} S =
-- --   (λ n → P₀ {S = S} (X (sequence S) n)) ,,
-- --   (λ {n : ℕ} x → P₁ (λ z → z) (π (sequence S) {n = suc n} x ))

-- -- postulate -- TODO
-- --   swap-Σ-∀ : ∀ {ℓ} (X : ℕ -> Set ℓ) (A : Set ℓ) (B : A -> Set ℓ) (p : {n : ℕ} -> Σ A (λ a -> B a -> X (suc n)) -> Σ A (λ a -> B a -> X n) -> Set ℓ) ->
-- --     (Σ (∀ (n : ℕ) -> Σ A (λ a -> B a -> X n)) (λ w -> (n : ℕ) -> p (w (suc n)) (w n))) ≡
-- --     (Σ ((n : ℕ) → A) λ a → Σ ((n : ℕ) → B (a n) → X n) λ u → (n : ℕ) -> p (a (suc n) , u (suc n)) (a n , u n))

-- --   todo-rules : ∀ {ℓ} (S : Container {ℓ}) -> (Σ ((n : ℕ) → S .fst) λ a → Σ ((n : ℕ) → S .snd (a n) → X (sequence S) n) λ u → (n : ℕ) -> P₁ {S = S} (π (sequence S) {n = n}) (a (suc n) , u (suc n)) ≡ (a n , u n)) ≡ P₀ {S = S} (M S)
-- --   -- equality of pairs, lemma 11, (Universal property of L)

-- -- -- Lemma 13
-- -- α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
-- -- α-iso {S = S} = 
-- --   (swap-Σ-∀ (X (sequence S)) (S .fst) (S .snd) λ {n} a b → (P₁ (π (sequence S) {n = n})) a ≡ b)
-- --   □ (todo-rules S)

-- -- -----------------------------------------------------
-- -- -- Shifting the limit of a chain is an equivalence --
-- -- -----------------------------------------------------

-- -- -- P commutes with limits
-- -- shift : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M S) ≡ M S
-- -- shift {S = S} = 
-- --   (sym α-iso) □ (L-unique {X,π = sequence S}) -- lemma 13 & lemma 12

-- -- -- Transporting along shift

-- -- in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M S) -> M S
-- -- in-fun {S = S} = transport (shift {S = S})

-- -- out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M S -> P₀ (M S)
-- -- out-fun {S = S} = transport (sym (shift {S = S}))

-- -- -- in-fun and out-fun are inverse

-- -- out-inverse-in : ∀ {ℓ} {S : Container {ℓ}} -> (out-fun ∘ in-fun {S = S}) ≡ idfun (P₀ (M S))
-- -- out-inverse-in i a = transport⁻Transport shift a i

-- -- in-inverse-out : ∀ {ℓ} {S : Container {ℓ}} -> (in-fun ∘ out-fun {S = S}) ≡ idfun (M S)
-- -- in-inverse-out = λ i a → transportTransport⁻ shift a i

-- -- -- constructor properties

-- -- in-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → P₀ (M S)} -> (in-fun ∘ f ≡ in-fun ∘ g) ≡ (f ≡ g)
-- -- in-inj = ≡-rel-a-inj in-fun out-fun in-inverse-out out-inverse-in

-- -- out-inj : ∀ {ℓ} {S : Container {ℓ}} {Z : Set ℓ} -> ∀ {f g : Z → M S} -> (out-fun ∘ f ≡ out-fun ∘ g) ≡ (f ≡ g)
-- -- out-inj = ≡-rel-b-inj in-fun out-fun in-inverse-out out-inverse-in

-- -- ---------------------------
-- -- -- Properties of M-types --
-- -- ---------------------------

-- -- Container-product : ∀ {ℓ} (_ _ : Container {ℓ}) -> Container {ℓ}
-- -- Container-product (A , B) (C , D) = (A × C , λ x → B (proj₁ x) × D (proj₂ x) )

-- -- P-product :
-- --   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
-- --   -> ((n : ℕ) -> W (A , B) n) × ((n : ℕ) -> W (C , D) n)
-- --   ------------------------
-- --   -> (n : ℕ) -> W (Container-product (A , B) (C , D)) n
-- -- P-product (x , y) 0 = lift tt
-- -- P-product (x , y) (suc n) = ((x (suc n) .fst) , (y (suc n) .fst)) , λ _ → P-product (x , y) n

-- -- P-product-inv₁ :
-- --   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
-- --   -> ((n : ℕ) -> W (Container-product (A , B) (C , D)) n)
-- --   ------------------------
-- --   -> (n : ℕ) -> W (A , B) n
-- -- P-product-inv₁ x 0 = lift tt
-- -- P-product-inv₁ {D = D} x (suc n) = (proj₁ (x (suc n) .fst)) , (λ _ → P-product-inv₁ {D = D} x n)

-- -- P-product-inv₂ :
-- --   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
-- --   -> ((n : ℕ) -> W (Container-product (A , B) (C , D)) n)
-- --   ------------------------
-- --   -> (n : ℕ) -> W (C , D) n
-- -- P-product-inv₂ x 0 = lift tt
-- -- P-product-inv₂ {B = B} x (suc n) = (proj₂ (x (suc n) .fst)) , (λ _ → P-product-inv₂ {B = B} x n)

-- -- P-product-inv :
-- --   ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
-- --   -> ((n : ℕ) -> W (Container-product (A , B) (C , D)) n)
-- --   ------------------------
-- --   -> ((n : ℕ) -> W (A , B) n) × ((n : ℕ) -> W (C , D) n)  
-- -- P-product-inv {B = B} {D = D} x = (P-product-inv₁ {D = D} x) , (P-product-inv₂ {B = B} x)

-- -- Product-split : ∀ {ℓ} {A B : Set ℓ} {x : A × B} -> ((proj₁ x , proj₂ x) ≡ x)
-- -- Product-split {x = a , b} = refl

-- -- -- (λ {(a , c) → isoToPath (iso (λ {(bf , df) (b , d) → (bf b) , (df d)})
-- -- --                                                    (λ f -> (λ x → proj₁ (f (x , {!!}))) , λ x → proj₂ (f ({!!} , x)))
-- -- --                                                    (λ b i → {!!})
-- -- --                                                    (λ {(x , y) i → x , y}))})

-- -- postulate
-- --   Σ-prod-fun :
-- --     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
-- --     → (n : ℕ)
-- --     → (x : A × C) 
-- --     → (B (proj₁ x) → W (A , B) n) × (D (proj₂ x) → W (C , D) n)
-- --     ≡ (B (proj₁ x) × D (proj₂ x) → W (A , B) n × W (C , D) n)

-- -- P-equality :
-- --     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
-- --     -> (n : ℕ)
-- --     ------------------------
-- --     -> (W (A , B) n × W (C , D) n)
-- --     ≡ (W (Container-product (A , B) (C , D)) n)
-- -- P-equality {A = A} {C} {B} {D} 0 = isoToPath (iso (λ _ → lift tt) (λ _ → lift tt , lift tt) (λ b i → lift tt) (λ {(_ , _) i → (lift tt) , (lift tt)}))
-- -- P-equality {A = A} {C} {B} {D} (suc n) =
-- --   W (A , B) (suc n) × W (C , D) (suc n)
-- --     ≡⟨ refl ⟩
-- --   Σ A (λ a → B a → W (A , B) n) × Σ C (λ c → D c → W (C , D) n)
-- --     ≡⟨ isoToPath (iso (λ {((a , c) , (b , d)) → (a , b) , (c , d)})
-- --                       (λ {((a , c) , (b , d)) → (a , b) , (c , d)})
-- --                       (λ {((a , c) , (b , d)) → refl})
-- --                       (λ { ((a , c) , b , d) → refl })) ⟩
-- --   Σ (A × C) (λ {(a , c) → (B a → W (A , B) n) × (D c → W (C , D) n)})
-- --     ≡⟨ Σ-ap-iso₂ (λ {(a , c) → Σ-prod-fun {A = A} {C = C} {B = B} {D = D} n (a , c)}) ⟩
-- --   Σ (A × C) (λ {(a , c) → B a × D c → W (A , B) n × W (C , D) n})
-- --     ≡⟨ Σ-ap-iso₂ (λ {(a , c) i → B a × D c → P-equality {B = B} {D = D} n i}) ⟩
-- --   Σ (A × C) (λ {(a , c) → B a × D c → W (Container-product (A , B) (C , D)) n})
-- --     ≡⟨ Σ-ap-iso₂ (λ {(a , c) → refl}) ⟩
-- --   W (Container-product (A , B) (C , D)) (suc n) ∎

-- -- postulate
-- --   π-equality :
-- --     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
-- --     -> (x : (n : ℕ) -> W (Container-product (A , B) (C , D)) n)
-- --     -> (n : ℕ)
-- --     ------------------------
-- --     -> πₙ (Container-product (A , B) (C , D)) (x (suc n))
-- --     ≡ x n

-- --   π-equality-2₁ :
-- --     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
-- --     -> (x : (n : ℕ) -> W (A , B) n × W (C , D) n)
-- --     -> (n : ℕ)
-- --     -----------------------
-- --     -> πₙ (A , B) (proj₁ (x (suc n)))
-- --     ≡ proj₁(x n)

-- --   π-equality-2₂ :
-- --     ∀ {ℓ} {A C : Set ℓ} {B : A -> Set ℓ} {D : C -> Set ℓ}
-- --     -> (x : (n : ℕ) -> W (A , B) n × W (C , D) n)
-- --     -> (n : ℕ)
-- --     -----------------------
-- --     -> πₙ (C , D) (proj₂ (x (suc n)))
-- --     ≡ proj₂(x n)

-- -- M-product : ∀ {ℓ} S T -> M {ℓ = ℓ} S × M T -> M (Container-product S T)
-- -- M-product S T (x , y) = (λ n → transport (P-equality n) (x .fst n , y .fst n)) , π-equality {B = S .snd} {D = T .snd} (λ n -> transport (P-equality n) (x .fst n , y .fst n))

-- -- M-product-inv : ∀ {ℓ} S T -> M (Container-product S T) -> M {ℓ = ℓ} S × M T
-- -- M-product-inv S T (x , y) = ((λ n → proj₁ (transport (sym (P-equality {B = S .snd} {D = T .snd} n)) (x n))) ,
-- --                                 π-equality-2₁ {B = S .snd} {D = T .snd} (λ n → transport (λ i → P-equality {B = S .snd} {D = T .snd} n (~ i)) (x n))) ,
-- --                              (λ n → proj₂ (transport (sym (P-equality {B = S .snd} {D = T .snd} n)) (x n))) ,
-- --                                 π-equality-2₂ {B = S .snd} {D = T .snd} (λ n → transport (λ i → P-equality {B = S .snd} {D = T .snd} n (~ i)) (x n))

-- -- postulate
-- --   M-product-iso₁ : ∀ {ℓ} (S T : Container {ℓ}) b -> M-product S T (M-product-inv S T b) ≡ b
-- --   M-product-iso₂ : ∀ {ℓ} (S T : Container {ℓ}) a -> M-product-inv S T (M-product S T a) ≡ a

-- -- M-product-equality : ∀ {ℓ} S T -> M {ℓ = ℓ} S × M T ≡ M (Container-product S T)
-- -- M-product-equality S T = isoToPath (iso (M-product S T) (M-product-inv S T) (M-product-iso₁ S T) (M-product-iso₂ S T))

-- -- ---------------------------
-- -- -- Function into M-types --
-- -- ---------------------------
