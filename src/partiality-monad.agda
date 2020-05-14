{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Container
open import Cubical.Codata.Sum

module partiality-monad where

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
Delay→Seq : ∀ {A} → Delay A → Seq A
Delay→Seq (now a) = (λ x → inl a) , (λ n → inl refl)
Delay→Seq (later x) = shift' (Delay→Seq (force x))
  where open ∞Delay

-- {-# NO_POSITIVITY_CHECK #-}
{-# TERMINATING #-} -- Do something about this!
Seq→Delay : ∀ {A} → Seq A → Delay A
Seq→Delay (g , a) = case g 0 of
  λ {(inr t) → later record { force = Seq→Delay (unshift (g , a)) }
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
Delay-Seq-retract : ∀ {A} (x : Seq A) → Delay→Seq (Seq→Delay x) ≡ x
Delay-Seq-retract (g , q) with g 0
... | (inl r) =
  let temp' = (eghtrkn (g , q) r temp) in
  ΣPathP (funExt (temp' .fst) , temp' .snd) 
  where
    postulate
      temp : inl r ≡ g 0
... | (inr tt) =
  ((shift' (Delay→Seq (Seq→Delay (unshift (g , q)))))
         ≡⟨ cong shift' (Delay-Seq-retract (unshift (g , q))) ⟩
  shift' (unshift (g , q))
         ≡⟨ temp ⟩
  shift (unshift (g , q)) (g 0 , q 0)
         ≡⟨ shift-unshift (g , q) ⟩ (g , q) ∎)
  -- ΣPathP ((fst (shift' (j (h (unshift (g , q))))) ≡⟨ cong (fst ∘ shift') (j-h (unshift (g , q))) ⟩ fst (shift' (unshift (g , q))) ≡⟨ {!!} ⟩ g ∎) , {!!})
  where
    open ∞Delay
    postulate
      temp : shift' (unshift (g , q)) ≡ shift (unshift (g , q)) (g 0 , q 0) -- = (g 0 ≡ inr tt)

module _ where
  mutual
    ∞j : ∀ {A} → P₀ {S = delay-S A} (delay A) → Seq A
    ∞j {A} (inl a , _) = (λ _ → inl a) , (λ _ → inl refl)
    ∞j {A} (inr tt , t) = shift' (j (t tt))
  
    j : ∀ {A} → (delay A) → Seq A
    j {A} = M-coinduction-const (Seq A) ∞j

  h-lift-x : ∀ {A} → Seq A → (n : ℕ) → W (delay-S A) n
  h-lift-x s 0 = lift tt
  h-lift-x s (suc n) = fst s 0 , λ _ → h-lift-x (unshift s) n
    
  h-lift-π : ∀ {A} → (t : Seq A) → (n : ℕ) → πₙ (delay-S A) (h-lift-x t (suc n)) ≡ (h-lift-x t n)
  h-lift-π s 0 = refl {x = lift tt}
  h-lift-π s (suc n) i = fst s 0 , λ _ → h-lift-π (unshift s) n i
  
  h : ∀ {A} → Seq A → delay A
  h s = (h-lift-x s) , (h-lift-π s)
  
  ∞h-j : ∀ {R} (b : P₀ {S = delay-S R} (delay R)) → h (j (in-fun b)) ≡ (in-fun b)
  ∞h-j (inl r , b) = {!!}
  ∞h-j (inr tt , t) = {!!}
  
  h-j : ∀ {R} (b : delay R) → h (j b) ≡ b
  h-j = M-coinduction {!!} ∞h-j
  
  j-h : ∀ {R} (b : Seq {R}) → j (h b) ≡ b
  j-h = ?
  
  Delay-Seq-Iso : ∀ {A} → Iso (Delay A) (Seq {A})
  Delay-Seq-Iso = (iso j h j-h h-j)
  
  Delay≡Seq : ∀ {A} → Delay A ≡ Seq {A}
  Delay≡Seq = isoToPath Delay-Seq-Iso

-- -----------------------
-- -- Sequence ordering --
-- -----------------------

open import Cubical.Data.Nat.Order

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
  {!!} -- TODO
  -- let temp : Σ[ m ∈ ℕ ] (isProp ((f m ≡ inl y) × (∀ n → (f n ≡ inr tt → ⊥) → m ≤ n)))
  --     temp = {!!}
  -- in
  -- λ x' y' → transport Σ-split ({!!} , {!!})
  -- where open import Cubical.Data.Nat.Order

Other-singleton : {a : Level} {A : Set a} → A → Set a
Other-singleton {A = A} x = Σ-syntax A λ y → x ≡ y

inspect : ∀ {A : Set} -> (x : A ⊎ Unit) → Other-singleton x
inspect (inl r) = (inl r) , refl
inspect (inr tt) = (inr tt) , refl

⇓′→⇓ : ∀ {A} x {y : A} → x ↓′ y → x ↓seq y
⇓′→⇓ = λ x x₁ → fst x₁ , proj₁ (snd x₁)
            
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

-- Partiality monad (QIIT)
-- Paper: Partiality, Revisited: The Partiality Monad as a Quotient Inductive-Inductive Type (https://arxiv.org/abs/1610.09254)
-- Authors: Thorsten Altenkirch, Nils Anders Danielsson, Nicolai Kraus
-- Formalization: http://www.cse.chalmers.se/~nad/listings/partiality-monad/Partiality-monad.Inductive.html
mutual
  infix 10 <_>⊥
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

-------------------------------------------------------------
-- Equivalence to Sequence quotiented by weak bisimularity --
-------------------------------------------------------------

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

  Increasing-at : ∀ {A : Set} → ℕ → (ℕ → A ⊎ Unit) → Set
  Increasing-at n f = LE (f n) (f (suc n))

  Increasing : ∀ {A : Set} → (ℕ → A ⊎ Unit) → Set
  Increasing f = ∀ n → Increasing-at n f

  ⊎-map : ∀ {a₁ a₂ b₁ b₂}
            {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂} →
          (A₁ → A₂) → (B₁ → B₂) → A₁ ⊎ B₁ → A₂ ⊎ B₂
  ⊎-map f g (inl x) = inl (f x)
  ⊎-map f g (inr x) = inr (g x)

  ≰→> : ∀ {m n} → (m ≤ n → ⊥) → n < m
  ≰→> {zero} {n} p = Cubical.Data.Empty.elim (p (zero-≤))
  ≰→> {suc m} {zero}  p = suc-≤-suc (zero-≤)
  ≰→> {suc m} {suc n} p = suc-≤-suc (≰→> (p ∘ suc-≤-suc))

  Dec : ∀ {p} → Set p → Set p
  Dec P = P ⊎ (P → ⊥)

  Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} →
              (A → B → Set ℓ) → Set (ℓ-max (ℓ-max a b) ℓ)
  Decidable _∼_ = ∀ x y → Dec (x ∼ y)

  _≤?_ : Decidable _≤_
  zero  ≤? n     = inl (zero-≤)
  suc m ≤? zero  = inr λ { x → ¬-<-zero x }
  suc m ≤? suc n = ⊎-map suc-≤-suc (λ m≰n → m≰n ∘ pred-≤-pred) (m ≤? n)

  ≤⊎> : ∀ m n → (m ≤ n) ⊎ (n < m)
  ≤⊎> m n = ⊎-map (idfun (Σ ℕ (λ z → z + m ≡ n))) ≰→> (m ≤? n)

  inj₁≢inj₂ : ∀ {A : Set} {B : Set} → {x : A} {y : B} → inl x ≡ inr y → ⊥
  inj₁≢inj₂ = true≢false ∘ cong λ {(inl x) → true ; (inr x) → false} -- cong (if_then true else false)

  postulate
    ↑-downwards-closed : ∀ {A} {f : ℕ → A ⊎ Unit} {m n} →
                         Increasing f → m ≤ n → f n ↑ → f m ↑
  -- ↑-downwards-closed = {!!}

  ↑<↓ : ∀ {A} {f : ℕ → A ⊎ Unit} {x m n} →
        Increasing f → (f m) ↑ → (f n) ↓ x → m < n
  ↑<↓ {A} {f} {x} {m} {n} inc fm↑ fn↓x with (≤⊎> n m)
  ... | inr m<n = m<n
  ... | inl n≤m = Cubical.Data.Empty.rec (inj₁≢inj₂ (inl x ≡⟨ sym fn↓x ⟩ f n ≡⟨ ↑-downwards-closed inc n≤m fm↑ ⟩ inr tt ∎))

  ≰→≥ : ∀ {m n} → (m ≤ n → ⊥) → n ≤ m
  ≰→≥ p = ≤-trans (≤-suc ≤-refl) (≰→> p)

  total : ∀ m n → (m ≤ n) ⊎ (n ≤ m)
  total m n = ⊎-map (idfun (Σ ℕ (λ z → z + m ≡ n))) ≰→≥ (m ≤? n)

  cancel-inj₁ : {A : Set} {B : Set} {x y : A} → _≡_ {A = A ⊎ B} (inl x) (inl y) → x ≡ y
  cancel-inj₁ {A} {B} {x = x} = λ p i → case p i of λ {(inl y) → const y x ; (inr y) → idfun A x}

  cancel-inj₂ : {A : Set} {B : Set} {x y : B} → _≡_ {A = A ⊎ B} (inr x) (inr y) → x ≡ y
  cancel-inj₂ {A} {B} {x = x} = λ p i → case p i of λ { (inr y) → const y x ; (inl y) → idfun B x }

  ↓-step : ∀ {A : Set} {f} {x : A} {n} →
           Increasing f → f n ↓ x → f (suc n) ↓ x
  ↓-step {f = f} {x} {n} inc fn↓x = step'' (inc n)
    module ↓ where
    step'' : LE (f n) (f (suc n)) → f (suc n) ↓ x
    step'' (inl fn≡f1+n) =
      f (suc n)  ≡⟨ sym fn≡f1+n ⟩
      f n        ≡⟨ fn↓x ⟩
      inl x     ∎
    step'' (inr (fn↑ , _)) =
      Cubical.Data.Empty.rec (inj₁≢inj₂ (inl x ≡⟨ sym fn↓x ⟩ f n ≡⟨ fn↑ ⟩ inr tt ∎))

  ↓-upwards-closed :
    ∀ {A} {f : ℕ → A ⊎ Unit} {m n x} →
    Increasing f → m ≤ n → f m ↓ x → f n ↓ x
  ↓-upwards-closed {A} {f} {x = x} inc (k , p) = ↓-upwards-closed-helper inc k p
    where
      ↓-upwards-closed-helper :
        ∀ {A} {f : ℕ → A ⊎ Unit} {m n x} →
        Increasing f → (k : ℕ) → (p : k + m ≡ n) → f m ↓ x → f n ↓ x
      ↓-upwards-closed-helper {A} {f} {x = x} _ 0 p = subst (λ a → f a ↓ x) p
      ↓-upwards-closed-helper {A} {f} {x = x} inc (suc n) p = subst (λ a → f a ↓ x) p ∘ ↓-step inc ∘ ↓-upwards-closed-helper inc n refl
    
  termination-value-unique :
    ∀ {A : Set} (x : Seq A) {y z} → x ↓seq y → x ↓seq z → y ≡ z
  termination-value-unique (f , inc) {y} {z} (m , fm↓y) (n , fn↓z)
    with total m n
  ... | inl m≤n = cancel-inj₁ (inl y ≡⟨ sym (↓-upwards-closed inc m≤n fm↓y) ⟩  f n ≡⟨ fn↓z ⟩ inl z ∎)
  ... | inr n≤m = cancel-inj₁ (inl y ≡⟨ sym fm↓y ⟩ f m ≡⟨ ↓-upwards-closed inc n≤m fn↓z ⟩ inl z ∎)
  
  ⇓→⇓′ : ∀ {A} x {y : A} → x ↓seq y → x ↓′ y
  ⇓→⇓′ x@(f , inc) = uncurry find-min
    where
      open import Cubical.Data.Nat.Order
      find-min : ∀ {y} m → f m ≡ inl y → x ↓′ y
      find-min 0 f0↓y = 0 , (f0↓y , (λ _ _ → zero-≤))
      find-min {y} (suc m) f-1+m↓y with inspect (f m)
      ... | (inr tt , fm↑) = (suc m) , (f-1+m↓y , 1+m-is-min)
        where
          1+m-is-min : ∀ n → (f n ≡ inr tt → ⊥) → m < n
          1+m-is-min n ¬fn↑ with inspect (f n)
          ... | (inr tt , fn↑) = Cubical.Data.Empty.elim (¬fn↑ fn↑)
          ... | (inl _ , fn↓) = ↑<↓ inc fm↑ fn↓
      ... | (inl y' , fm↓y') =
        let temp = find-min m fm↓y' in
        temp .fst , with-other-value (proj₁ (temp .snd)) , proj₂ (temp .snd)
        where
          with-other-value : ∀ {n} → f n ↓ y' → f n ↓ y
          with-other-value = subst (_ ↓_) (termination-value-unique x (_ , fm↓y') (_ , f-1+m↓y))

  ↓⇔∥↓∥ : ∀ {A} → isSet A → ∀ x {y : A} → (x ↓seq y → ∥ x ↓seq y ∥) × (∥ x ↓seq y ∥ → x ↓seq y)
  ↓⇔∥↓∥ A-set x {y} =
    (∣_∣) ,
    let temp = Cubical.HITs.PropositionalTruncation.rec (⇓′-propositional A-set x {y = y}) (⇓→⇓′ x) in
    λ x₁ → let temp' = temp x₁ in ⇓′→⇓ x temp'

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
      
  seq/∼→⊥ : ∀ {A} → isSet A → (Seq A / _∼seq_) → < A >⊥
  seq/∼→⊥ {A} A-set = recc Seq→⊥ (λ {x y} → Delay→⊥-≈→≡ A-set x y) ⊥-is-set

  ⊥→seq/∼ : ∀ {A} → isSet A → < A >⊥ → (Seq A / _∼seq_)
  ⊥→seq/∼ {A} A-set never = [ (λ x → inr tt) , (λ n → inl refl) ]
  ⊥→seq/∼ {A} A-set (η a) = [ (λ x → inl a) , (λ n → inl refl) ]
  ⊥→seq/∼ {A} A-set (⊔ (f , p)) = [ (λ x → let temp = f x in {!!}) , (λ n → {!!}) ] -- Σ[ f ∈ (ℕ → < A >⊥) ] ((n : ℕ) → f n ⊑ f (suc n))
  ⊥→seq/∼ {A} A-set (α a b i) = eq/ {!!} {!!} {!!} {!!}
  ⊥→seq/∼ {A} A-set (⊥-is-set x y a b i j) = squash/ (⊥→seq/∼ A-set x) (⊥→seq/∼ A-set y) (cong (⊥→seq/∼ A-set) a) (cong (⊥→seq/∼ A-set) b) i j

  ⊥-⊥-Iso : ∀ {A} → isSet A → Iso (Seq A / _∼seq_) < A >⊥
  ⊥-⊥-Iso A-set = iso (seq/∼→⊥ A-set) (⊥→seq/∼ A-set) {!!} {!!}

-------------------------------------------------------------------------
-- Alternative definition of partiality monad using HITs and not HIITs --
-------------------------------------------------------------------------

-- Another Partiality monad (HIT)
-- Paper: Quotienting the Delay Monad by Weak Bisimilarity (https://niccoloveltri.github.io/mscs_final.pdf)
-- Authors: James Chapman, Tarmo Uustalu and Niccoló Veltri
-- Formalization: http://cs.ioc.ee/~niccolo/delay/
mutual
  -- free countably-complete join semilattice
  data P∞ (X : Type₀) : Type₀ where
     η : X → P∞ X
     ⊥ : P∞ X
     ⋁ : (ℕ → P∞ X) → P∞ X    

     v-sym : ∀ {x y} → (x v y) ≡ (y v x)
     v-assoc : ∀ {x y z} → x v (y v z) ≡ (x v y) v z
     v-now : ∀ {x} → x v x ≡ x
     v-never : ∀ {x} → x v ⊥ ≡ x
     v-⋁ : ∀ {s : ℕ → P∞ X} (n : ℕ) → (s n) v (⋁ s) ≡ ⋁ s
     v-⋁' : ∀ {s : ℕ → P∞ X} {x} → ((⋁ s) v x) ≡ (⋁ λ n → s n v x)

     P∞-set : isSet (P∞ X)

     -- f1 : ?

  _v_ : ∀ {X} (x y : P∞ X) → P∞ X
  x v y = ⋁ (λ {0 → x ; (suc n) → y})

  _≤_ : ∀ {X} (x y : P∞ X) → Type₀
  x ≤ y = (x v y) ≡ y

S' = P∞ Unit

Pₛ-Container : Container
Pₛ-Container = S' , λ x → x ≡ η tt -- (η tt ≡ ⊤)

Pₛ-M-type : Set -- What is this??
Pₛ-M-type = M Pₛ-Container

Pₛ : Type₀ → Type₀
Pₛ = P₀ {S = Pₛ-Container}

-- if S is the free ωcppo on 1, then Pₛ X is the free ωcppo on X

h : ∀ {X} → X → Pₛ X
h x = (η tt) , (λ _ → x)

