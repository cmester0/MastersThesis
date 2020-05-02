{-# OPTIONS --cubical --guardedness #-} --safe

open import itree
open import M
open import Coalg

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Sum
open import Cubical.Data.Empty
-- open import Cubical.Data.Bool
open import Cubical.Data.Prod

-- open import Cubical.Codata.Stream

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Functions.FunExtEquiv

-- open import Cubical.Relation.Binary

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

-- open import Cubical.Foundations.Transport

open import Container
open import helper

-- open import Cubical.Data.Nat.Order

module bisim-examples where

-- -------------------------------
-- -- The identity bisimulation --
-- -------------------------------

-- Δ : ∀ {ℓ} {S : Container {ℓ}} -> bisimulation S M-coalg (_≡_)
-- αᵣ (Δ {S = S}) (a , b , r) = fst (out-fun a) , (λ x → snd (out-fun a) x , (snd (out-fun a) x , refl {x = snd (out-fun a) x}))
-- rel₁ (Δ {S = S}) = funExt λ {(a , b , r) → refl {x = out-fun a}}
-- rel₂ (Δ {S = S}) = funExt λ {(a , b , r) → cong (out-fun) (sym r)}

-- ---------------------------------------------
-- -- Strong Bisimulation for the delay monad --
-- ---------------------------------------------

-- mutual
--   data _∼_ {R} : (x y : delay R) → Set where
--     ∼now   : ∀ {r} → delay-ret r ∼ delay-ret r
--     ∼later : ∀ {x y} → x ∞∼ y → (delay-tau x) ∼ (delay-tau y)

--   record _∞∼_ {R} (x y : delay R) : Set where
--     coinductive
--     field
--       force : x ∼ y

-- open _∞∼_ public

-- delay-bisim : ∀ {R} → bisimulation (delay-S R) M-coalg _∼_
-- αᵣ (delay-bisim) (a , b , ∼now {r}) = inl r , λ ()
-- αᵣ (delay-bisim) (a , b , ∼later {x} {y} p) = inr tt , λ _ → x , y , force p
-- rel₁ (delay-bisim) i (a , b , (∼now {r})) = out-inverse-in i (inl r , λ ())
-- rel₁ (delay-bisim) i (a , b , (∼later {x} {y} p)) = out-inverse-in i (inr tt , λ _ → x)
-- rel₂ (delay-bisim) i (a , b , (∼now {r})) = out-inverse-in i (inl r , λ ())
-- rel₂ (delay-bisim) i (a , b , (∼later {x} {y} p)) = out-inverse-in i (inr tt , λ _ → y)

-- delay-coinduction : ∀ {R} {m m'} → m ∼ m' → m ≡ m'
-- delay-coinduction {R} = coinduction (_∼_ {R}) delay-bisim

-- -------------------------------------------
-- -- Weak Bisimulation for the delay monad --
-- -------------------------------------------

-- mutual
--   data _≈_ {R} : (x y : delay R) → Set where
--     ≈now : ∀ {x : R} → delay-ret x ≈ delay-ret x
--     ≈later : ∀ {x y : delay R} → x ∞≈ y → (delay-tau x) ≈ (delay-tau y)
--     ≈laterˡ : ∀ {x y : delay R} → x ≈ y → (delay-tau x) ≈ y
--     ≈laterʳ : ∀ {x y : delay R} → x ≈ y → x ≈ (delay-tau y)

--   record _∞≈_ {R} (x y : delay R) : Set where
--     coinductive
--     field
--       force : x ≈ y

-- open _∞≈_

-- weak-delay-bisim : ∀ {R} → bisimulation (delay-S R) M-coalg _≈_
-- αᵣ (weak-delay-bisim) (a , b , ≈now {r}) = inl r , λ ()
-- αᵣ (weak-delay-bisim) (a , b , ≈later {x} {y} p) = inr tt , λ _ → x , y , force p
-- αᵣ (weak-delay-bisim) (a , b , ≈laterˡ {x} {y} p) = inr tt , λ _ → x , y , p
-- αᵣ (weak-delay-bisim) (a , b , ≈laterʳ {x} {y} p) = inr tt , λ _ → x , y , p
-- rel₁ (weak-delay-bisim) i (a , b , (≈now {r})) = out-inverse-in i (inl r , λ ())
-- rel₁ (weak-delay-bisim) i (a , b , (≈later {x} {y} p)) = out-inverse-in i (inr tt , λ _ → x)
-- rel₁ (weak-delay-bisim) i (a , b , (≈laterˡ {x} {y} p)) = (out-fun (in-fun {!!}) ≡⟨ {!!} ⟩ {!!} ∎) i
-- rel₁ (weak-delay-bisim) i (a , b , (≈laterʳ {x} {y} p)) = out-inverse-in {!!} (inr tt , λ _ → x)
-- rel₂ (weak-delay-bisim) i (a , b , (≈now {r})) = out-inverse-in i (inl r , λ ())
-- rel₂ (weak-delay-bisim) i (a , b , (≈later {x} {y} p)) = out-inverse-in i (inr tt , λ _ → y)
-- rel₂ (weak-delay-bisim) i (a , b , (≈laterˡ {x} {y} p)) = {!!}
-- rel₂ (weak-delay-bisim) i (a , b , (≈laterʳ {x} {y} p)) = {!!}

-- weak-delay-coinduction : ∀ {R} {m m' : delay R} → m ≈ m' → m ≡ m'
-- weak-delay-coinduction = {!!}

-- -------------------
-- -- Partial order --
-- -------------------

-- mutual
--   data _d⊑_ {A} : delay A → delay A → Set where
--     now-cong : ∀ {x} → (delay-ret x) d⊑ (delay-ret x)
--     laterʳ   : ∀ {x y} → x d⊑ y tt → x d⊑ in-fun (inr tt , y)
--     laterˡ   : ∀ {x y} → x ∞d⊑ y → delay-tau x d⊑ y

--   record _∞d⊑_ {A} (x y : delay A) : Set where
--     coinductive
--     field
--       force : x d⊑ y

-- open _∞d⊑_

-- --------------
-- -- Sequence --
-- --------------

module _ where
  ismon : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → Set
  ismon {A} g = (n : ℕ) → (g n ≡ g (suc n))
              ⊎ ((g n ≡ inr tt) × ((g (suc n) ≡ inr tt) → ⊥))

  ismon' : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → ℕ → Set
  ismon' {A} g n = (g n ≡ g (suc n))
                 ⊎ ((g n ≡ inr tt) × ((g (suc n) ≡ inr tt) → ⊥))

  Seq : ∀ {A : Set} → Set
  Seq {A} = (Σ (ℕ → A ⊎ Unit) (λ g → ismon g))

  postulate
    inl-inr-disjoint : ∀ {ℓ} {A : Set ℓ} (x : A) → inl x ≡ inr tt → ⊥

  -- shift-1 : ∀ {A} → Seq {A} → Seq {A}
  -- fst (shift-1 (g , a)) 0 = inr tt -- should this be g 0 ?
  -- fst (shift-1 (g , a)) (suc n) = g n 
  -- snd (shift-1 (g , a)) 0 =
  --   case a 0 return (λ x → ismon' (fst (shift-1 (g , (λ { 0 → x ; (suc n) → a (suc n) })))) 0) of
  --     λ {(inr v) → inl (sym (proj₁ v))
  --       ;(inl v) → case g 0 return (λ x → ismon' (λ { 0 → inr tt ; (suc 0) → x ; (suc (suc n)) → g (suc n) }) 0) of
  --                       λ { (inl j) → inr (refl , inl-inr-disjoint j)
  --                         ; (inr tt) → inl refl}}
  -- snd (shift-1 (g , a)) (suc n) = a n

  -- shift-0 : ∀ {A} → Seq {A} → Seq {A}
  -- fst (shift-0 (g , a)) 0 = g 0
  -- fst (shift-0 (g , a)) (suc n) = g n
  -- snd (shift-0 (g , a)) 0 = inl refl
  -- snd (shift-0 (g , a)) (suc n) = a n

  -- shift : ∀ {A} → (va : A ⊎ Unit) → (t : Seq {A}) → Seq {A}
  -- shift (inr tt) = shift-1
  -- shift (inl r) = shift-0

  -- shift-unshift-helper : ∀ {A} → (t : Seq {A}) → (x : ℕ) → fst (shift (fst t 0) (unshift t)) x ≡ fst t x
  -- shift-unshift-helper (g , a) 0 with a 0
  -- shift-unshift-helper (g , a) 0 | (inl v) with g 0
  -- ... | (inr tt) = refl
  -- ... | (inl m) = sym v
  -- shift-unshift-helper (g , a) 0 | (inr v) =
  --   fst (shift (g 0) (g ∘ suc , a ∘ suc)) 0 
  --     ≡⟨ cong (λ k → fst (shift k (g ∘ suc , a ∘ suc)) 0) (proj₁ v) ⟩
  --   inr tt
  --     ≡⟨ sym (proj₁ v) ⟩
  --   g 0 ∎
  -- shift-unshift-helper (g , a) (suc n) with g 0
  -- ... | (inl r) = refl
  -- ... | (inr tt) = refl
  
  -- shift-unshift : ∀ {A} t → shift {A = A} (fst t 0) (unshift t) ≡ t
  -- shift-unshift (g , a) =
  --   ΣPathP (funExt (shift-unshift-helper (g , a)) , temp)
  --   where
  --     postulate
  --       temp : PathP (λ i → ismon (funExt (shift-unshift-helper (g , a)) i)) (snd (shift (g 0) (unshift (g , a)))) a

  shift : ∀ {A} → (t : Seq {A}) → Σ (A ⊎ Unit) (λ va → ismon' (λ {0 → va ; (suc n) → fst t n}) 0) → Seq {A}
  shift (g , a) (va , mon) = (λ {0 → va ; (suc n) → g n}) , (λ {0 → mon ; (suc n) → a n})

  shift' : ∀ {A} → Seq {A} → Seq {A}
  shift' t =
    shift t
      ((inr tt) ,
      (case (fst t 0) return (λ x → ismon' (λ { 0 → (inr tt) ; (suc 0) → x ; (suc (suc n)) → fst t n }) 0) of
        λ {(inl r) → inr (refl , inl-inr-disjoint r)
          ;(inr tt) → inl refl}))

  unshift : ∀ {A} → Seq {A} → Seq {A}
  unshift (g , a) = g ∘ suc , a ∘ suc
  
  -- works for any -- (fst t 0)
  unshift-shift : ∀ {A} t {va-mon} → unshift {A = A} (shift t va-mon) ≡ t
  unshift-shift {A = A} (g , a) = refl

  shift-unshift : ∀ {A} t → shift {A = A} (unshift t) (fst t 0 , snd t 0) ≡ t
  shift-unshift (g , a) =
    ΣPathP ((funExt λ {0 → refl ; (suc n) → refl }) , λ {i 0 → a 0 ; i (suc n) → a (suc n)})

-- ----------------------------------
-- -- Sequence equivalent to Delay --
-- ----------------------------------

-- -- module _ where
-- --   abstract
-- --     mutual
-- --       ∞j : ∀ {A} → P₀ {S = delay-S A} (delay A) → Seq {A}
-- --       ∞j {A} (inl a , _) = (λ _ → inl a) , (λ _ → inl refl)
-- --       ∞j {A} (inr tt , t) = shift (inr tt) (j (t tt))
    
-- --       j : ∀ {A} → (delay A) → Seq {A}
-- --       j {A} = M-coinduction-const (Seq {A}) ∞j
    
-- --     h-lift-x : ∀ {A} → Seq {A} → (n : ℕ) → W (delay-S A) n
-- --     h-lift-x s 0 = lift tt
-- --     h-lift-x s (suc n) = fst s 0 , λ _ → h-lift-x (unshift s) n
    
-- --     h-lift-π : ∀ {A} → (t : Seq {A}) → (n : ℕ) → πₙ (delay-S A) (h-lift-x t (suc n)) ≡ (h-lift-x t n)
-- --     h-lift-π s 0 = refl {x = lift tt}
-- --     h-lift-π s (suc n) i = fst s 0 , λ _ → h-lift-π (unshift s) n i
  
-- --     h : ∀ {A} → Seq {A} → delay A
-- --     h s = (h-lift-x s) , (h-lift-π s)
  
-- --     ∞h-j : ∀ {R} (b : P₀ {S = delay-S R} (delay R)) → h (j (in-fun b)) ≡ (in-fun b)
-- --     ∞h-j (inl r , b) = {!!}
-- --     ∞h-j (inr tt , t) = {!!}
  
-- --     h-j : ∀ {R} (b : delay R) → h (j b) ≡ b
-- --     h-j = M-coinduction {!!} ∞h-j
  
-- --     j-h : ∀ {R} (b : Seq {R}) → j (h b) ≡ b
-- --     j-h = ?
  
-- --   Delay-Seq-Iso : ∀ {A} → Iso (Delay A) (Seq {A})
-- --   Delay-Seq-Iso = (iso j h j-h h-j)
  
-- --   Delay≡Seq : ∀ {A} → Delay A ≡ Seq {A}
-- --   Delay≡Seq = isoToPath Delay-Seq-Iso

-- -----------------------
-- -- Sequence ordering --
-- -----------------------

-- _↓seq_ : ∀ {A} → Seq {A} → A → Set
-- s ↓seq a = Σ ℕ λ n → fst s n ≡ inl a

-- _⊑seq_ : ∀ {A} → ∀ (_ _ : Seq {A}) → Set
-- _⊑seq_ {A} s t = (a : A) → ∥ s ↓seq a ∥ → ∥ t ↓seq a ∥

-- _∼seq_ : ∀ {A} → ∀ (_ _ : Seq {A}) → Set
-- s ∼seq t = s ⊑seq t × t ⊑seq s

-- postulate -- TODO
--   delay-set-quotiented : ∀ R → (delay R) / (_≈_ {R}) ≡ (Seq {R}) / (_∼seq_ {R})
-- -- delay-set-quotiented R = {!!} -- equality by eq/

-- ----------------------
-- -- Partiality monad --
-- ----------------------

record partiality-monad {ℓ} {ℓ'} {A : Set (ℓ-max ℓ ℓ')} : Set (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    A⊥ : Set ℓ'
    _⊑_ : A⊥ → A⊥ → Set ℓ'

    -- set-trunc : (x y : A⊥) (p q : x ≡ y) → p ≡ q

    η : A → A⊥
    ⊥ₐ : A⊥
    ⊔ : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)) → A⊥

    ⊑-refl : ∀ (x : A⊥) → x ⊑ x
    ⊑-trans : ∀ (x y z : A⊥) → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-⊥ : ∀ (x) → ⊥ₐ ⊑ x

    α : (x y : A⊥) → x ⊑ y → y ⊑ x → x ≡ y

    ⊑-prop : isProp ({x y : A⊥} → x ⊑ y)
    ⊑-0 : {(s , p) : Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)} → (n : ℕ) → s n ⊑ ⊔ (s , p)
    ⊑-1 : {(s , p) : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n))} → (x : A⊥) → (n : ℕ) → s n ⊑ x → ⊔ (s , p) ⊑ x

open partiality-monad

-- -- w : ∀ {A} → Seq {A} → partiality-monad {A}
-- -- w {A} (s , q) = record
-- --               { A⊥ = Σ ((x : ℕ) → A ⊎ Unit)
-- --                        (λ z →
-- --                           (x : ℕ) →
-- --                           (z x ≡ z (suc x)) ⊎
-- --                           ((z x ≡ inr tt) × ((x₁ : z (suc x) ≡ inr tt) → ⊥)))
-- --               ; _⊑_ = _⊑seq_ {A = A}
-- --               ; η = λ _ → s , q
-- --               ; ⊥ₐ = s , q
-- --               ; ⊔ = λ _ → s , q
-- --               ; ⊑-refl = λ x a z → z
-- --               ; ⊑-trans = λ x y z z₁ z₂ a z₃ → z₂ a (z₁ a z₃)
-- --               ; ⊑-⊥ = {!!}
-- --               ; α = {!!}
-- --               ; ⊑-prop = {!!}
-- --               ; ⊑-0 = {!!}
-- --               ; ⊑-1 = {!!}
-- --               }

-- never : ∀ {R} → delay R
-- never = lift-to-M-general (λ _ → inr tt) (λ _ → refl {x = inr tt})

-- later-cong : ∀ {R} {x : delay R} {y} → x ∞d⊑ y tt → (delay-tau x) d⊑ in-fun (inr tt , y)
-- later-cong p = laterʳ (laterˡ p)

-- postulate
--   sadf : ∀ {R} → never {R = R} ≡ delay-tau never

-- mutual
--   neverLE : ∀ {R} (x : delay R) → never d⊑ x
--   neverLE = M-coinduction (λ y → never d⊑ y)
--     λ {(inl r , b) → transport (cong (λ a → a d⊑ in-fun (inl r , b)) (sym sadf)) (laterˡ (∞neverLE (in-fun (inl r , b))))
--       ;(inr tt , t) → {!!}}

--   ∞neverLE : ∀ {R} (x : delay R) → never ∞d⊑ x
--   force (∞neverLE x) = neverLE x

-- delay-to-partiality : ∀ {R} → delay R → {_⊑'_ : R → R → Set} → partiality-monad {R} -- partiality not R ⊎ Unit !
-- A⊥ (delay-to-partiality {R} a) = delay R
-- _⊑_ (delay-to-partiality {R} a) = _d⊑_
-- η (delay-to-partiality {R} a) = delay-ret
-- ⊥ₐ (delay-to-partiality {R} a) = never
-- ⊔ (delay-to-partiality {R} a) = {!!}
-- ⊑-refl (delay-to-partiality {R} a) = {!!} -- d⊑-refl
-- ⊑-trans (delay-to-partiality {R} a) = {!!}
-- ⊑-⊥ (delay-to-partiality {R} a) = M-coinduction (λ x → never d⊑ x) λ {(inl r , b) → {!!} ; (inr tt , t) → {!!}}
-- α (delay-to-partiality {R} a) = {!!}
-- ⊑-prop (delay-to-partiality {R} a) = {!!}
-- ⊑-0 (delay-to-partiality {R} a) = {!!}
-- ⊑-1 (delay-to-partiality {R} a) = {!!}

-- -- asg : ∀ {R n} → inl tt ≡ limit-collapse {S = delay-S R} (λ _ → Unit ⊎ R) (λ _ x → x) (inl tt) n
-- -- asg {R} {0} = refl
-- -- asg {R} {suc n} = asg {R} {n}

-- -- never-inf-delay₁ : ∀ {R} → ∀ n → never {R} .fst n ≡ delay-tau never .fst n
-- -- never-inf-delay₁ {R} 0 i = lift tt
-- -- never-inf-delay₁ {R} (suc 0) = ΣPathP (asg {n = (suc 0)} , refl)
-- -- never-inf-delay₁ {R} (suc (suc n)) = ΣPathP (asg {n = (suc (suc n))} ,
-- --   let temp' = (λ _ → lift-x-general (λ _ → inl tt) (suc n)) in
-- --   let temp = transport (λ i → delay-helper R ((α-iso-step-5-Iso-helper0 {S = delay-S R} (limit-collapse {S = delay-S R} (λ _ → Unit ⊎ R) (λ _ x → x) (inl tt)) (λ n₁ _ → limit-collapse {S = delay-S R} (λ _ → Unit ⊎ R) (λ _ x → x) (inl tt) n₁) n) (~ i)) → W (delay-S R) (suc n)) (transport (λ i → Unit → Container.W (delay-S R) (suc n)) (λ z → lift-x-general (λ _ → inl tt) (suc n)))
-- --    in {!!}) -- never {R} .fst n

-- postulate
--   never-inf-delay : ∀ {R} → never {R} ≡ delay-tau never
-- -- never-inf-delay = transport (Σ-split) ((λ i n → never-inf-delay₁ n i) , {!!})

-- -- postulate
-- --   never-inf-delay : ∀ {R} → never {R} ≡ delay-tau never

-- -- -- limit-collapse (λ _ → Unit ⊎ R) (λ _ x → x) (Iso.fun sym-α-iso-step-6 (inl tt , (λ _ → never)) .fst) n

-- data _↓_ {R : Set}: delay R → R → Set where
--   now↓ : ∀ (x : R) (b : ⊥ → delay R) → in-fun (inl x , b) ↓ x
--   later↓ : ∀ (x : R) (y : delay R) → y ↓ x → delay-tau y ↓ x

-- mutual
--   data _d⊑_ {R} : delay R → delay R → Set where
--     ⊑now-now : ∀ {x : delay R} {r : R} {b : ⊥ → delay R} → x d⊑ in-fun (inl r , b) -- problem using a function, not a constructor, though delay-ret should be a constructor?!
--     -- ⊑later0 : ∀ t u → in-fun (inl tt , t) d⊑ in-fun (inl tt , u) → t tt d⊑ u tt
--     -- ⊑later : ∀ t u → in-fun (out-fun (t tt)) ∞d⊑ in-fun (out-fun (u tt)) → in-fun (inl tt , t) d⊑ in-fun (inl tt , u)
--     -- ⊑later-weak : ∀ x t → t tt ∞d⊑ x → in-fun (inl tt , t) d⊑ x
--     -- ⊑never : ∀ x → never d⊑ x

--   record _∞d⊑_ {R} (x y : delay R) : Set where
--     coinductive
--     field
--       force : x d⊑ y

-- open _∞d⊑_

-- -- d⊑-refl : ∀ {R} (x : delay R) → x d⊑ x
-- -- d⊑-refl = M-coinduction (λ x → x d⊑ x) d⊑-refl-helper
-- --   where
-- --     mutual
-- --       d⊑-refl-helper : ∀ {R} (x : P₀ (delay R)) → in-fun x d⊑ in-fun x
-- --       d⊑-refl-helper (inr r , b) = ⊑now-now r r b b refl
-- --       d⊑-refl-helper (inl tt , t) = ⊑later t t (∞d⊑-refl-helper (out-fun (t tt)))

-- --       ∞d⊑-refl-helper : ∀ {R} (x : P₀ (delay R)) → in-fun x ∞d⊑ in-fun x
-- --       force (∞d⊑-refl-helper x) = d⊑-refl-helper x

-- -- postulate
-- --   jhok : ∀ {R} (x : delay R) a b → x ↓ a → x ↓ b → a ≡ b

-- -- d⊑-trans-helper : ∀ {R} (x : delay R) (y : P₀ {S = delay-S R} (delay R)) (z : delay R) → x d⊑ in-fun y → in-fun y d⊑ z → x d⊑ z
-- -- d⊑-trans-helper x (inr r , b) z p q = {!!}

-- -- mutual
-- --   ∞delay≈-refl-helper : ∀ {R} (x₁ P₀ (M (delay-S R))) → ∞delay≈ (in-fun x₁) (in-fun x₁)
-- --   force (∞delay≈-refl-helper x) = delay≈-refl-helper x

-- --   delay≈-refl-helper : ∀ {R} (x₁ P₀ (M (delay-S R))) → delay≈ (in-fun x₁) (in-fun x₁)
-- --   delay≈-refl-helper (inr r , b) = EqNow
-- --   delay≈-refl-helper (inl tt , b) = EqLater (∞delay≈-refl-helper (out-fun (b tt)))

-- -- delay≈-refl : ∀ {R} {x} -> delay≈ {R} x x
-- -- delay≈-refl {R = R} {x = x} = delay≈-in-out (case out-fun x return (λ x₁ → delay≈ (in-fun x₁) (in-fun x₁)) of delay≈-refl-helper)

-- -- -----------------------------------------------
-- -- -- Delay Set-Quotiented by Weak Bisimulation --
-- -- -----------------------------------------------

-- -- delay-set-quotiented : ∀ R → Set
-- -- delay-set-quotiented R = (delay R) / (_≈_ {R}) -- equality by eq/

-- -- -- delay-set-quotiented-bisim' : ∀ R → ∀ (x y : delay R) → (([ x ] ≡ [ y ]) ≡ (x ≈ y))
-- -- -- delay-set-quotiented-bisim' R x y = isoToPath (iso {!!} (λ x₁ → cong ([_] {R = _≈_}) (weak-delay-coinduction x₁)) {!!} {!!})

-- -- weak-delay-prop : ∀ {R} → BinaryRelation.isPropValued (_≈_ {R = R}) -- {R = _≈_}
-- -- weak-delay-prop x y = {!!}

-- -- weak-delay-isEquivRel : ∀ {R} → BinaryRelation.isEquivRel (_≈_ {R = R}) -- {R = _≈_}
-- -- weak-delay-isEquivRel = {!!}

-- -- delay-set-quotiented-bisim : ∀ R → ∀ (x y : delay R) → (([ x ] ≡ [ y ]) ≡ (x ≈ y))
-- -- delay-set-quotiented-bisim R x y = ua (isEquivRel→isEffective {R = _≈_} weak-delay-prop weak-delay-isEquivRel x y)

-- -- -- (isEquivRel→isEffective ? ? x y)

-- record partiality-monad {A : Set} : Set₁ where
--   field
--     A⊥ : Set
--     _⊑_ : A⊥ → A⊥ → Set

--     -- set-trunc : (x y : A⊥) (p q : x ≡ y) → p ≡ q

--     η : A → A⊥
--     ⊥ₐ : A⊥
--     ⊔ : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)) → A⊥

--     ⊑-refl : ∀ (x : A⊥) → x ⊑ x
--     ⊑-trans : ∀ (x y z : A⊥) → x ⊑ y → y ⊑ z → x ⊑ z
--     ⊑-⊥ : ∀ (x) → ⊥ₐ ⊑ x

--     α : (x y : A⊥) → x ⊑ y → y ⊑ x → x ≡ y

--     ⊑-prop : isProp ({x y : A⊥} → x ⊑ y)
--     ⊑-0 : {(s , p) : Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)} → (n : ℕ) → s n ⊑ ⊔ (s , p)
--     ⊑-1 : {(s , p) : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n))} → (x : A⊥) → (n : ℕ) → s n ⊑ x → ⊔ (s , p) ⊑ x

-- open partiality-monad
