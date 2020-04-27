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

-- open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Functions.FunExtEquiv

-- open import Cubical.Relation.Binary

-- open import Cubical.HITs.SetQuotients

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
-- αᵣ (delay-bisim) (a , b , ∼now {r}) = inr r , λ ()
-- αᵣ (delay-bisim) (a , b , ∼later {x} {y} p) = inl tt , λ _ → x , y , force p
-- rel₁ (delay-bisim) i (a , b , (∼now {r})) = out-inverse-in i (inr r , λ ())
-- rel₁ (delay-bisim) i (a , b , (∼later {x} {y} p)) = out-inverse-in i (inl tt , λ _ → x)
-- rel₂ (delay-bisim) i (a , b , (∼now {r})) = out-inverse-in i (inr r , λ ())
-- rel₂ (delay-bisim) i (a , b , (∼later {x} {y} p)) = out-inverse-in i (inl tt , λ _ → y)

-- delay-coinduction : ∀ {R} {m m'} → m ∼ m' → m ≡ m'
-- delay-coinduction {R} = coinduction (_∼_ {R}) delay-bisim

-- -------------------------------------------
-- -- Weak Bisimulation for the delay monad --
-- -------------------------------------------

-- record _≈_ {R} (x y : delay R) : Set where
--   coinductive
--   field
--     sim : x ∼ y
--     rel : ∀ (x : delay R) → x ≡ delay-tau x

-- open _≈_

-- weak-delay-coinduction : ∀ {R} {m m' : delay R} → m ≈ m' → m ≡ m'
-- weak-delay-coinduction {R} p = delay-coinduction (sim p)

record partiality-monad {A : Set} : Set₁ where
  field
    A⊥ : Set
    _⊑_ : A⊥ → A⊥ → Set

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

never : ∀ {R} → delay R
never = lift-to-M-general (λ _ → inl tt) (λ _ → refl {x = inl tt})

-- asg : ∀ {R n} → inl tt ≡ limit-collapse {S = delay-S R} (λ _ → Unit ⊎ R) (λ _ x → x) (inl tt) n
-- asg {R} {0} = refl
-- asg {R} {suc n} = asg {R} {n}

-- never-inf-delay₁ : ∀ {R} → ∀ n → never {R} .fst n ≡ delay-tau never .fst n
-- never-inf-delay₁ {R} 0 i = lift tt
-- never-inf-delay₁ {R} (suc 0) = ΣPathP (asg {n = (suc 0)} , refl)
-- never-inf-delay₁ {R} (suc (suc n)) = ΣPathP (asg {n = (suc (suc n))} ,
--   let temp' = (λ _ → lift-x-general (λ _ → inl tt) (suc n)) in
--   let temp = transport (λ i → delay-helper R ((α-iso-step-5-Iso-helper0 {S = delay-S R} (limit-collapse {S = delay-S R} (λ _ → Unit ⊎ R) (λ _ x → x) (inl tt)) (λ n₁ _ → limit-collapse {S = delay-S R} (λ _ → Unit ⊎ R) (λ _ x → x) (inl tt) n₁) n) (~ i)) → W (delay-S R) (suc n)) (transport (λ i → Unit → Container.W (delay-S R) (suc n)) (λ z → lift-x-general (λ _ → inl tt) (suc n)))
--    in {!!}) -- never {R} .fst n

postulate
  never-inf-delay : ∀ {R} → never {R} ≡ delay-tau never
-- never-inf-delay = transport (Σ-split) ((λ i n → never-inf-delay₁ n i) , {!!})

-- postulate
--   never-inf-delay : ∀ {R} → never {R} ≡ delay-tau never

-- -- limit-collapse (λ _ → Unit ⊎ R) (λ _ x → x) (Iso.fun sym-α-iso-step-6 (inl tt , (λ _ → never)) .fst) n

data _↓_ {R : Set}: delay R → R → Set where
  now↓ : ∀ (x : R) (b : ⊥ → delay R) → in-fun (inr x , b) ↓ x
  later↓ : ∀ (x : R) (y : delay R) → y ↓ x → delay-tau y ↓ x

mutual
  data _d⊑_ {R} : delay R → delay R → Set where
    ⊑now-now : ∀ {x : delay R} {r : R} {b : ⊥ → delay R} → x d⊑ in-fun (inr r , b) -- problem using a function, not a constructor, though delay-ret should be a constructor?!
    -- ⊑later0 : ∀ t u → in-fun (inl tt , t) d⊑ in-fun (inl tt , u) → t tt d⊑ u tt
    -- ⊑later : ∀ t u → in-fun (out-fun (t tt)) ∞d⊑ in-fun (out-fun (u tt)) → in-fun (inl tt , t) d⊑ in-fun (inl tt , u)
    -- ⊑later-weak : ∀ x t → t tt ∞d⊑ x → in-fun (inl tt , t) d⊑ x
    -- ⊑never : ∀ x → never d⊑ x

  record _∞d⊑_ {R} (x y : delay R) : Set where
    coinductive
    field
      force : x d⊑ y

open _∞d⊑_

-- d⊑-refl : ∀ {R} (x : delay R) → x d⊑ x
-- d⊑-refl = M-coinduction (λ x → x d⊑ x) d⊑-refl-helper
--   where
--     mutual
--       d⊑-refl-helper : ∀ {R} (x : P₀ (delay R)) → in-fun x d⊑ in-fun x
--       d⊑-refl-helper (inr r , b) = ⊑now-now r r b b refl
--       d⊑-refl-helper (inl tt , t) = ⊑later t t (∞d⊑-refl-helper (out-fun (t tt)))

--       ∞d⊑-refl-helper : ∀ {R} (x : P₀ (delay R)) → in-fun x ∞d⊑ in-fun x
--       force (∞d⊑-refl-helper x) = d⊑-refl-helper x

postulate
  jhok : ∀ {R} (x : delay R) a b → x ↓ a → x ↓ b → a ≡ b

d⊑-trans-helper : ∀ {R} (x : delay R) (y : P₀ {S = delay-S R} (delay R)) (z : delay R) → x d⊑ in-fun y → in-fun y d⊑ z → x d⊑ z
d⊑-trans-helper x (inr r , b) z (⊑now-now) q = {!!}

-- mutual
--   ∞delay≈-refl-helper : ∀ {R} (x₁ P₀ (M (delay-S R))) → ∞delay≈ (in-fun x₁) (in-fun x₁)
--   force (∞delay≈-refl-helper x) = delay≈-refl-helper x

--   delay≈-refl-helper : ∀ {R} (x₁ P₀ (M (delay-S R))) → delay≈ (in-fun x₁) (in-fun x₁)
--   delay≈-refl-helper (inr r , b) = EqNow
--   delay≈-refl-helper (inl tt , b) = EqLater (∞delay≈-refl-helper (out-fun (b tt)))

-- delay≈-refl : ∀ {R} {x} -> delay≈ {R} x x
-- delay≈-refl {R = R} {x = x} = delay≈-in-out (case out-fun x return (λ x₁ → delay≈ (in-fun x₁) (in-fun x₁)) of delay≈-refl-helper)

delay-to-partiality : ∀ {R} → delay R → {_⊑'_ : R → R → Set} → partiality-monad {R} -- partiality not R ⊎ Unit !
A⊥ (delay-to-partiality {R} a) = delay R
_⊑_ (delay-to-partiality {R} a) = _d⊑_
η (delay-to-partiality {R} a) = delay-ret
⊥ₐ (delay-to-partiality {R} a) = never
⊔ (delay-to-partiality {R} a) = {!!}
⊑-refl (delay-to-partiality {R} a) = ? -- d⊑-refl
⊑-trans (delay-to-partiality {R} a) = {!!}
⊑-⊥ (delay-to-partiality {R} a) = {!!}
α (delay-to-partiality {R} a) = {!!}
⊑-prop (delay-to-partiality {R} a) = {!!}
⊑-0 (delay-to-partiality {R} a) = {!!}
⊑-1 (delay-to-partiality {R} a) = {!!}

-- -----------------------------------------------
-- -- Delay Set-Quotiented by Weak Bisimulation --
-- -----------------------------------------------

-- delay-set-quotiented : ∀ R → Set
-- delay-set-quotiented R = (delay R) / (_≈_ {R}) -- equality by eq/

-- -- delay-set-quotiented-bisim' : ∀ R → ∀ (x y : delay R) → (([ x ] ≡ [ y ]) ≡ (x ≈ y))
-- -- delay-set-quotiented-bisim' R x y = isoToPath (iso {!!} (λ x₁ → cong ([_] {R = _≈_}) (weak-delay-coinduction x₁)) {!!} {!!})

-- weak-delay-prop : ∀ {R} → BinaryRelation.isPropValued (_≈_ {R = R}) -- {R = _≈_}
-- weak-delay-prop x y = {!!}

-- weak-delay-isEquivRel : ∀ {R} → BinaryRelation.isEquivRel (_≈_ {R = R}) -- {R = _≈_}
-- weak-delay-isEquivRel = {!!}

-- delay-set-quotiented-bisim : ∀ R → ∀ (x y : delay R) → (([ x ] ≡ [ y ]) ≡ (x ≈ y))
-- delay-set-quotiented-bisim R x y = ua (isEquivRel→isEffective {R = _≈_} weak-delay-prop weak-delay-isEquivRel x y)

-- -- (isEquivRel→isEffective ? ? x y)

-- --------------
-- -- Sequence --
-- --------------

-- ismon : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → Set
-- ismon g = (n : ℕ)
--   → (g n ≡ g (suc n))
--   ⊎ ((g n ≡ inr tt) × ((g (suc n) ≡ inr tt) → ⊥))

-- Seq : ∀ {A : Set} → Set
-- Seq {A} = (Σ (ℕ → A ⊎ Unit) ismon)

-- asda : ∀ (A : Set) (g : ℕ → A ⊎ Unit) (a : ismon g) → ismon {A = A} (λ {0 → inr tt ; (suc n) → g n})
-- asda A g a 0 = inr {!!}
-- asda A g a (suc n) = inl {!!}

-- shift : ∀ {A} → Seq {A} → Seq {A}
-- shift (g , a) =
--   (λ {0 → inr tt ; (suc n) → g n}) ,
--   {!!}

-- -- case g 0 return (λ x → {!!}) of λ x → {!!}

-- unshift : ∀ {A} → Seq {A} → Seq {A}
-- unshift (g , a) = g ∘ suc , a ∘ suc

-- j : ∀ {A} → delay A → Seq {A}
-- j {A} m = case out-fun m return (λ x → Seq {A}) of
--   λ {(inr a , b) → (λ x → inl a) , (λ n → inl refl)
--     ;(inl tt , t) → shift (j (t tt))}


-- -- h : ∀ {A} → Seq {A} → delay A
-- -- h (g , a) with g 0
-- -- ... | (inl r) = delay-ret r
-- -- ... | (inr _) = delay-tau (h (unshift (g , a)))

-- -- ksd : ∀ {A} b → h {A} (j b) ≡ b
-- -- ksd b =
-- --   transport (λ i → h (j (in-inverse-out i b)) ≡ in-inverse-out i b)
-- --   (case out-fun b return (λ x → h (j (in-fun x)) ≡ in-fun x) of λ {(inr a , c) →
-- --     h (j (in-fun (inr a , c))) ≡⟨ {!!} ⟩ delay-ret a ≡⟨ {!!} ⟩ in-fun (inr a , c) ∎})

-- -- delay-is-seq : ∀ {R} → delay R ≡ Seq {R}
-- -- delay-is-seq = isoToPath (iso j h (λ b → {!!}) {!!})

-- ----------------------
-- -- Partiality monad --
-- ----------------------

-- record partiality-monad (A : Set) : Set₁ where
--   field
--     A⊥ : Set
--     _⊑_ : A⊥ → A⊥ → Set

--     η : A → A⊥
--     ⊥ₐ : A⊥
--     ⊔ : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)) → A⊥
--     α : (x y : A⊥) → x ⊑ y → y ⊑ x → x ≡ y

--     ⊑-refl : ∀ {x : A⊥} → x ⊑ x
--     ⊑-trans : ∀ {x y z : A⊥} → x ⊑ y → y ⊑ z → x ⊑ z
--     ⊑-⊥ : ∀ {x} → ⊥ₐ ⊑ x

--     ⊑-prop : isProp ({x y : A⊥} → x ⊑ y)
--     ⊑-0 : {(s , p) : Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)} → (n : ℕ) → s n ⊑ ⊔ (s , p)
--     ⊑-1 : {(s , p) : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n))} → (x : A⊥) → (n : ℕ) → s n ⊑ x → ⊔ (s , p) ⊑ x

--     -- quotient : ∀ x y → x ⊑ y 

-- open partiality-monad

-- remove-tau : {!!}

-- partiality-monad-delay : ∀ {R} → partiality-monad R
-- A⊥ (partiality-monad-delay {R}) = {!!}
-- _⊑_ (partiality-monad-delay {R}) x y = {!!}

-- η (partiality-monad-delay {R}) x = 1 , ((inr x , λ ()) , λ x₁ → inr x , λ ())
-- ⊥ₐ (partiality-monad-delay) = 0 , lift tt , λ x₁ → lift tt -- never
-- -- ⊔ (partiality-monad-delay) (f , m) = (λ n → f n .fst n) , (λ n → f (suc n) .snd n ∙ cong (λ a → a .fst n) (sym (weak-delay-coinduction (m n))))
-- -- α (partiality-monad-delay) x y z w = weak-delay-coinduction z

-- ⊑-refl (partiality-monad-delay) = {!!}
-- ⊑-trans (partiality-monad-delay) x y = {!!}
-- ⊑-⊥ (partiality-monad-delay) = {!!} , {!!}

-- never-x : ∀ {R} n → X (sequence (delay-S R)) n
-- never-x 0 = lift tt
-- never-x (suc n) = inl tt , λ _ → never-x n

-- never-π : ∀ {R} n → π (sequence (delay-S R)) (never-x (suc n)) ≡ never-x n
-- never-π 0 = refl {x = lift tt}
-- never-π (suc n) i = inl tt , λ _ → never-π n i

-- never : ∀ {R} → delay R
-- never = never-x , never-π
