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

  Seq : Set → Set
  Seq A = (Σ (ℕ → A ⊎ Unit) (λ g → ismon g))

  postulate
    inl-inr-disjoint : ∀ {ℓ} {A : Set ℓ} (x : A) → inl x ≡ inr tt → ⊥

  shift : ∀ {A} → (t : Seq A) → Σ (A ⊎ Unit) (λ va → ismon' (λ {0 → va ; (suc n) → fst t n}) 0) → Seq A
  shift (g , a) (va , mon) = (λ {0 → va ; (suc n) → g n}) , (λ {0 → mon ; (suc n) → a n})

  shift' : ∀ {A} → Seq A → Seq A
  shift' t =
    shift t
      ((inr tt) ,
      (case (fst t 0) return (λ x → ismon' (λ { 0 → (inr tt) ; (suc 0) → x ; (suc (suc n)) → fst t n }) 0) of
        λ {(inl r) → inr (refl , inl-inr-disjoint r)
          ;(inr tt) → inl refl}))

  unshift : ∀ {A} → Seq A → Seq A
  unshift (g , a) = g ∘ suc , a ∘ suc
  
  -- works for any -- (fst t 0)
  unshift-shift : ∀ {A} t {va-mon} → unshift {A = A} (shift t va-mon) ≡ t
  unshift-shift {A = A} (g , a) = refl

  shift-unshift : ∀ {A} t → shift {A = A} (unshift t) (fst t 0 , snd t 0) ≡ t
  shift-unshift (g , a) =
    ΣPathP ((funExt λ {0 → refl ; (suc n) → refl }) , λ {i 0 → a 0 ; i (suc n) → a (suc n)})

----------------------------------
-- Sequence equivalent to Delay --
----------------------------------

{-# TERMINATING #-} -- Do something about this!
j : ∀ {A} → Delay A → Seq A
j (now a) = (λ x → inl a) , (λ n → inl refl)
j (later x) = shift' (j (force x))
  where open ∞Delay

-- {-# NO_POSITIVITY_CHECK #-}
{-# TERMINATING #-} -- Do something about this!
h : ∀ {A} → Seq A → Delay A
h (g , a) = case g 0 of
  λ {(inr t) → later record { force = h (unshift (g , a)) }
    ;(inl r) → now r}

case-0_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : ℕ → A) (B : A → Type ℓ') → (∀ x → B x) → B (x 0)
case-0 x return P of f = f (x 0)

postulate
  htrr : ∀ {ℓ} {A : Set ℓ} {r : A} → inl r ≡ inr tt → ⊥

{-# TERMINATING #-}
eghtrkn :
  ∀ {A} (x : Seq A) → (r : A) → (inl r ≡ fst x 0) →
    (Σ (∀ n → inl r ≡ fst x n) λ p →
      PathP (λ x₁ → ∀ n → (p n x₁ ≡ p (suc n) x₁) ⊎ ((p n x₁ ≡ inr tt) × (p (suc n) x₁ ≡ inr tt → ⊥)))
        (λ n → inl (refl {x = inl r}))
        (snd x))
fst (eghtrkn (g , q) r p) 0 = p
fst (eghtrkn (g , q) r p) (suc n) with q n
... | (inl v) = fst (eghtrkn (g , q) r p) n ∙ v
... | (inr (t , t')) = Cubical.Data.Empty.elim (htrr (fst (eghtrkn (g , q) r p) n ∙ t)) -- contradiction
snd (eghtrkn (g , q) r p) = temp
  where
    postulate
      temp : PathP
        (λ x₁ →
          (n : ℕ) →
          (fst (eghtrkn (g , q) r p) n x₁ ≡
            fst (eghtrkn (g , q) r p) (suc n) x₁)
          ⊎
          ((fst (eghtrkn (g , q) r p) n x₁ ≡ inr tt) ×
            (fst (eghtrkn (g , q) r p) (suc n) x₁ ≡ inr tt → ⊥)))
        (λ n → inl refl) q

{-# TERMINATING #-}
j-h : ∀ {A} (x : Seq A) → j (h x) ≡ x
j-h (g , q) with g 0
... | (inl r) =
  let temp' = (eghtrkn (g , q) r temp) in
  ΣPathP (funExt (temp' .fst) , temp' .snd) 
  where
    postulate
      temp : inl r ≡ g 0
... | (inr tt) =
  ((shift' (j (h (unshift (g , q))))) ≡⟨ cong shift' (j-h (unshift (g , q))) ⟩ shift' (unshift (g , q)) ≡⟨ temp ⟩ shift (unshift (g , q)) (g 0 , q 0) ≡⟨ shift-unshift (g , q) ⟩ (g , q) ∎)
  -- ΣPathP ((fst (shift' (j (h (unshift (g , q))))) ≡⟨ cong (fst ∘ shift') (j-h (unshift (g , q))) ⟩ fst (shift' (unshift (g , q))) ≡⟨ {!!} ⟩ g ∎) , {!!})
  where
    open ∞Delay
    postulate
      temp : shift' (unshift (g , q)) ≡ shift (unshift (g , q)) (g 0 , q 0) -- = (g 0 ≡ inr tt)
  
  -- ΣPathP (({!!} ≡⟨ {!!} ⟩ {!!} ∎) , {!!})
  -- case g 0 return ? of {!!}
  -- ΣPathP (((λ n → inl r) ≡⟨ funExt (eghtrkn ((λ {0 → inl r ; (suc n) → g (suc n)}) , {!!}) r refl) ⟩ (λ { 0 → inl r ; (suc n) → g (suc n) }) ≡⟨ {!!} ⟩ g ∎) , {!!})

  -- transport {!!}
  -- (case q 0 return (λ x → j (h (g , (λ {0 → x ; (suc n) → q (suc n)}))) ≡ {!!}) of {!!})
  -- -- case g 0 return (λ x → j (h ((λ { 0 → {!!} ; (suc n) → g (suc n) }) , λ {0 → {!!} ; (suc n) → {!!}})) ≡ {!!}) of λ {(inl r) → {!!} ; (inr r) → {!!}}

-- module _ where
--   abstract
--     mutual
--       ∞j : ∀ {A} → P₀ {S = delay-S A} (delay A) → Seq {A}
--       ∞j {A} (inl a , _) = (λ _ → inl a) , (λ _ → inl refl)
--       ∞j {A} (inr tt , t) = shift' (j (t tt))
    
--       j : ∀ {A} → (delay A) → Seq {A}
--       j {A} = M-coinduction-const (Seq {A}) ∞j

--     h-lift-x : ∀ {A} → Seq {A} → (n : ℕ) → W (delay-S A) n
--     h-lift-x s 0 = lift tt
--     h-lift-x s (suc n) = fst s 0 , λ _ → h-lift-x (unshift s) n
    
--     h-lift-π : ∀ {A} → (t : Seq {A}) → (n : ℕ) → πₙ (delay-S A) (h-lift-x t (suc n)) ≡ (h-lift-x t n)
--     h-lift-π s 0 = refl {x = lift tt}
--     h-lift-π s (suc n) i = fst s 0 , λ _ → h-lift-π (unshift s) n i
  
--     h : ∀ {A} → Seq {A} → delay A
--     h s = (h-lift-x s) , (h-lift-π s)
  
--     ∞h-j : ∀ {R} (b : P₀ {S = delay-S R} (delay R)) → h (j (in-fun b)) ≡ (in-fun b)
--     ∞h-j (inl r , b) = {!!}
--     ∞h-j (inr tt , t) = {!!}
  
--     h-j : ∀ {R} (b : delay R) → h (j b) ≡ b
--     h-j = M-coinduction {!!} ∞h-j
  
--     j-h : ∀ {R} (b : Seq {R}) → j (h b) ≡ b
--     j-h = ?
  
--   Delay-Seq-Iso : ∀ {A} → Iso (Delay A) (Seq {A})
--   Delay-Seq-Iso = (iso j h j-h h-j)
  
--   Delay≡Seq : ∀ {A} → Delay A ≡ Seq {A}
--   Delay≡Seq = isoToPath Delay-Seq-Iso

-- -----------------------
-- -- Sequence ordering --
-- -----------------------

_↓seq_ : ∀ {A} → Seq A → A → Set
s ↓seq a = Σ ℕ λ n → fst s n ≡ inl a

_⊑seq_ : ∀ {A} → ∀ (_ _ : Seq A) → Set
_⊑seq_ {A} s t = (a : A) → ∥ s ↓seq a ∥ → ∥ t ↓seq a ∥

_∼seq_ : ∀ {A} → ∀ (_ _ : Seq A) → Set
s ∼seq t = s ⊑seq t × t ⊑seq s

_↓′_ : ∀ {A} → Seq A → A → Set _
(f , _) ↓′ y = Σ[ m ∈ ℕ ] ((f m ≡ inl y) × (∀ n → (f n ≡ inr tt → ⊥) → m ≤ n))
  where open import Cubical.Data.Nat.Order

⇓′-propositional : ∀ {A} → isSet A → ∀ x {y : A} → isProp (x ↓′ y)
⇓′-propositional A-set x@(f , _) {y} =
  let temp : Σ[ m ∈ ℕ ] (isProp ((f m ≡ inl y) × (∀ n → (f n ≡ inr tt → ⊥) → m ≤ n)))
      temp = {!!} , {!!}
  in
  λ x' y' → transport Σ-split ({!!} , {!!})
  where open import Cubical.Data.Nat.Order

⇓′→⇓ : ∀ {A} x {y : A} → x ↓′ y → x ↓seq y
⇓′→⇓ = λ x x₁ → fst x₁ , proj₁ (snd x₁)

⇓→⇓′ : ∀ {A} x {y : A} → x ↓seq y → x ↓′ y
⇓→⇓′ x@(f , inc) = uncurry {!!} -- find-min
  -- where
  -- find-min : ∀ {y} m → f m ↓ y → x ⇓′ y
  -- find-min     zero    f0↓y    = zero , f0↓y , λ _ _ → N.zero≤ _
  -- find-min {y} (suc m) f-1+m↓y with inspect (f m)
  -- ... | nothing , fm↑ = suc m , f-1+m↓y , 1+m-is-min
  --   where
  --   1+m-is-min : ∀ n → ¬ f n ↑ → m N.< n
  --   1+m-is-min n ¬fn↑ with inspect (f n)
  --   ... | nothing , fn↑ = ⊥-elim (¬fn↑ fn↑)
  --   ... | just _  , fn↓ = ↑<↓ inc fm↑ fn↓
  -- ... | just y′ , fm↓y′ =
  --            $⟨ find-min m fm↓y′ ⟩
  --   x ⇓′ y′  ↝⟨ Σ-map id (Σ-map with-other-value id) ⟩□
  --   x ⇓′ y   □
  --   where
  --   with-other-value : ∀ {n} → f n ↓ y′ → f n ↓ y
  --   with-other-value =
  --     subst (_ ↓_)
  --           (termination-value-unique x (_ , fm↓y′) (_ , f-1+m↓y))
            
↓⇔∥↓∥ : ∀ {A} → isSet A → ∀ x {y : A} → (x ↓seq y → ∥ x ↓seq y ∥) × (∥ x ↓seq y ∥ → x ↓seq y)
↓⇔∥↓∥ A-set x {y} =
  (∣_∣) ,
  let temp = Cubical.HITs.PropositionalTruncation.rec (⇓′-propositional A-set x {y = y}) (⇓→⇓′ x) in
  λ x₁ → let temp' = temp x₁ in ⇓′→⇓ x temp'

-- ⇓⇔∥⇓∥ : Is-set A → ∀ x {y : A} → x ⇓ y ⇔ x ∥⇓∥ y
-- ⇓⇔∥⇓∥ A-set x {y} = record
--   { to   = ∣_∣
--   ; from = x ∥⇓∥ y  ↝⟨ Trunc.rec (⇓′-propositional A-set x) (⇓→⇓′ x) ⟩
--            x ⇓′ y   ↝⟨ Σ-map id proj₁ ⟩□
--            x ⇓ y    □
--   }
  
----------------------
-- Partiality monad --
----------------------

-- Partiality monad
-- Paper: Partiality, Revisited: The Partiality Monad as a Quotient Inductive-Inductive Type (https://arxiv.org/abs/1610.09254)
-- Authors: Thorsten Altenkirch, Nils Anders Danielsson, Nicolai Kraus
-- Formalization: http://www.cse.chalmers.se/~nad/listings/partiality-monad/Partiality-monad.Inductive.html
mutual
  infix 10 _⊥
  infix 4  _⊑_

  abstract
    -- The partiality monad.

    data <_>⊥ {ℓ} (A : Type ℓ) : Type ℓ where
      never  : < A >⊥
      η      : A → < A >⊥
      ⊔      : Increasing-sequence A → < A >⊥
      α      : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
      ⊥-is-set : isSet (< A >⊥)

  -- Increasing sequences.

  Increasing-sequence : ∀ {ℓ} → Type ℓ → Type ℓ
  Increasing-sequence A = Σ[ f ∈ (ℕ → < A >⊥) ] ((n : ℕ) → f n ⊑ f (suc n))

  -- Upper bounds.

  Is-upper-bound : ∀ {ℓ} → {A : Type ℓ} → Increasing-sequence A → < A >⊥ → Set ℓ
  Is-upper-bound s x = ∀ n → (fst s n) ⊑ x

  -- A projection function for Increasing-sequence.
  
  abstract
    -- An ordering relation.

    data _⊑_ {ℓ} {A : Set ℓ} : < A >⊥ → < A >⊥ → Set ℓ where
      ⊑-refl            : ∀ x → x ⊑ x
      ⊑-trans           : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
      never⊑            : ∀ x → never ⊑ x
      upper-bound       : ∀ s → Is-upper-bound s (⊔ s)
      least-upper-bound : ∀ s ub → Is-upper-bound s ub → ⊔ s ⊑ ub
      ⊑-propositional   : ∀ {x y} → isProp (x ⊑ y)

abstract
  Maybe→⊥ : ∀ {A : Type₀} → A ⊎ Unit → < A >⊥
  Maybe→⊥ (inr tt)  = never
  Maybe→⊥ (inl y) = η y

  infix 4 _↑ _↓_

  -- x ↓ y means that the computation x has the value y.

  _↓_ : ∀ {A : Set} → A ⊎ Unit → A → Set
  x ↓ y = x ≡ inl y

  -- x ↑ means that the computation x does not have a value.

  _↑ :  ∀ {A : Set} → A ⊎ Unit → Set
  x ↑ = x ≡ inr tt

  LE : ∀ {A : Set} → A ⊎ Unit → A ⊎ Unit → Set
  LE x y = (x ≡ y) ⊎ ((x ↑) × (y ↑ → ⊥))

  Maybe→⊥-mono : ∀ {A : Type₀} {x y : A ⊎ Unit} → LE x y → (Maybe→⊥ x) ⊑ (Maybe→⊥ y)
  Maybe→⊥-mono {x = x} {y} (inl p) = subst (λ a → Maybe→⊥ x ⊑ Maybe→⊥ a) p (⊑-refl (Maybe→⊥ x))
  Maybe→⊥-mono {x = x} {y} (inr p) = subst (λ a → Maybe→⊥ a ⊑ Maybe→⊥ y) (sym (proj₁ p)) (never⊑ (Maybe→⊥ y))

  Seq→Inc-seq : ∀ {A} → Seq A → Increasing-sequence A
  Seq→Inc-seq (f , inc) = Maybe→⊥ ∘ f , Maybe→⊥-mono ∘ inc

  -- Turns increasing sequences of potential values into partial values.

  Seq→⊥ : ∀ {A} → Seq A → < A >⊥
  Seq→⊥ = ⊔ ∘ Seq→Inc-seq

  -- If every element in one increasing sequence is bounded by some
  -- element in another, then the least upper bound of the first
  -- sequence is bounded by the least upper bound of the second one.
  private
    ⊑→⨆⊑⨆ : ∀ {A : Set} {s₁ s₂ : Increasing-sequence A} {f : ℕ → ℕ} →
            (∀ n → fst s₁ n ⊑ fst s₂ (f n)) → ⊔ s₁ ⊑ ⊔ s₂
    ⊑→⨆⊑⨆ {s₁} {s₂} {f} s₁⊑s₂ =
      least-upper-bound _ _ λ n → ⊑-trans (s₁⊑s₂ n) (upper-bound _ _)

  -- A variant of the previous lemma.

  private
    ∃⊑→⨆⊑⨆ : ∀ {A : Set} {s₁ s₂ : Increasing-sequence A} →
             (∀ m → Σ[ n ∈ ℕ ] (fst s₁  m ⊑ fst s₂ n)) → ⊔ s₁ ⊑ ⊔ s₂
    ∃⊑→⨆⊑⨆ s₁⊑s₂ = ⊑→⨆⊑⨆ (snd ∘ s₁⊑s₂)

  Other-singleton : {a : Level} {A : Set a} → A → Set a
  Other-singleton {A = A} x = Σ-syntax A λ y → x ≡ y

  inspect : ∀ {A : Set} -> (x : A ⊎ Unit) → Other-singleton x
  inspect (inl r) = (inl r) , refl
  inspect (inr tt) = (inr tt) , refl
  
  Seq→⊥-mono : ∀ {A : Set} → isSet A → ∀ (x y : Seq A) → x ⊑seq y → Seq→⊥ x ⊑ Seq→⊥ y
  Seq→⊥-mono A-set x@(f , _) y@(g , _) x⊑y =
    ∃⊑→⨆⊑⨆ inc
    where
      inc : ∀ m → Σ[ n ∈ ℕ ] (Maybe→⊥ (f m) ⊑ Maybe→⊥ (g n))
      inc m with inspect (f m)
      ... | (inr tt , p) = 0 , subst (λ x₁ → Maybe→⊥ x₁ ⊑ Maybe→⊥ (g 0)) (sym p) (never⊑ (Maybe→⊥ (g 0))) -- never⊑ (Maybe→⊥ (g 0))
      ... | (inl r , p) = fst y↓z , subst (λ a → Maybe→⊥ (f m) ⊑ Maybe→⊥ a) (sym (snd y↓z))
                                    (subst (λ a → Maybe→⊥ a ⊑ η r) (sym p) (⊑-refl (η r)))
        where
          y↓z : y ↓seq r
          y↓z = let temp = x⊑y r in let temp' = proj₂ (↓⇔∥↓∥ A-set y) ∘ temp in temp' ∣ m , p ∣
    
  Delay→⊥-≈→≡ : ∀ {A} → isSet A → ∀ (x y : Seq A) → x ∼seq y → Seq→⊥ x ≡ Seq→⊥ y
  Delay→⊥-≈→≡ A-set x y (p , q) = α (Seq→⊥-mono A-set x y p) (Seq→⊥-mono A-set y x q)

  recc :
    ∀ {A B : Set} {R : A → A → Set} →
    (f : A → B) →
    (∀ {x y} → R x y → f x ≡ f y) →
    isSet B →
    A / R → B
  recc f g s [ x ] = f x
  recc f g s (eq/ _ _ r i) = g r i
  recc f g s (squash/ x y p q i j) = s (recc f g s x) (recc f g s y) (cong (λ a → recc f g s a) p) (cong (λ a → recc f g s a) q) i j
      
  ⊥→⊥ : ∀ {A} → isSet A → (Seq A / _∼seq_) → < A >⊥
  ⊥→⊥ {A} A-set = recc Seq→⊥ (λ {x y} → Delay→⊥-≈→≡ A-set x y) ⊥-is-set
          
postulate
  never-terminate-does-not-terminate : ∀ {A} (x : A) → ∥ ((λ x₁ → inr tt) , (λ n → inl (λ _ → inr tt))) ↓seq x ∥ → ⊥

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
