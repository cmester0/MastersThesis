{-# OPTIONS --cubical --guardedness #-} --safe

open import itree
open import M
open import Coalg

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Prod

open import Cubical.Codata.Stream

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Binary

open import Cubical.HITs.SetQuotients

open import Container
open import helper

open import Cubical.Data.Nat.Order

module bisim-examples where

-------------------------------
-- The identity bisimulation --
-------------------------------

Δ : ∀ {ℓ} {S : Container {ℓ}} -> bisimulation S M-coalg (_≡_)
αᵣ (Δ {S = S}) (a , b , r) = fst (out-fun a) , (λ x → snd (out-fun a) x , (snd (out-fun a) x , refl {x = snd (out-fun a) x}))
rel₁ (Δ {S = S}) = funExt λ {(a , b , r) → refl {x = out-fun a}}
rel₂ (Δ {S = S}) = funExt λ {(a , b , r) → cong (out-fun) (sym r)}

---------------------------------------------
-- Strong Bisimulation for the delay monad --
---------------------------------------------

mutual
  data _∼_ {R} : (x y : delay R) → Set where
    ∼now   : ∀ {r} → delay-ret r ∼ delay-ret r
    ∼later : ∀ {x y} → x ∞∼ y → (delay-tau x) ∼ (delay-tau y)

  record _∞∼_ {R} (x y : delay R) : Set where
    coinductive
    field
      force : x ∼ y

open _∞∼_ public

delay-bisim : ∀ {R} → bisimulation (delay-S R) M-coalg _∼_
αᵣ (delay-bisim) (a , b , ∼now {r}) = inr r , λ ()
αᵣ (delay-bisim) (a , b , ∼later {x} {y} p) = inl tt , λ _ → x , y , force p
rel₁ (delay-bisim) i (a , b , (∼now {r})) = out-inverse-in i (inr r , λ ())
rel₁ (delay-bisim) i (a , b , (∼later {x} {y} p)) = out-inverse-in i (inl tt , λ _ → x)
rel₂ (delay-bisim) i (a , b , (∼now {r})) = out-inverse-in i (inr r , λ ())
rel₂ (delay-bisim) i (a , b , (∼later {x} {y} p)) = out-inverse-in i (inl tt , λ _ → y)

delay-coinduction : ∀ {R} {m m'} → m ∼ m' → m ≡ m'
delay-coinduction {R} = coinduction (_∼_ {R}) delay-bisim

-------------------------------------------
-- Weak Bisimulation for the delay monad --
-------------------------------------------

record _≈_ {R} (x y : delay R) : Set where
  coinductive
  field
    sim : x ∼ y
    rel : ∀ (x : delay R) → x ≡ delay-tau x

open _≈_

weak-delay-coinduction : ∀ {R} {m m' : delay R} → m ≈ m' → m ≡ m'
weak-delay-coinduction {R} p = delay-coinduction (sim p)

-----------------------------------------------
-- Delay Set-Quotiented by Weak Bisimulation --
-----------------------------------------------

delay-set-quotiented : ∀ R → Set
delay-set-quotiented R = (delay R) / (_≈_ {R}) -- equality by eq/

-- delay-set-quotiented-bisim' : ∀ R → ∀ (x y : delay R) → (([ x ] ≡ [ y ]) ≡ (x ≈ y))
-- delay-set-quotiented-bisim' R x y = isoToPath (iso {!!} (λ x₁ → cong ([_] {R = _≈_}) (weak-delay-coinduction x₁)) {!!} {!!})

weak-delay-prop : ∀ {R} → BinaryRelation.isPropValued (_≈_ {R = R}) -- {R = _≈_}
weak-delay-prop x y = {!!}

weak-delay-isEquivRel : ∀ {R} → BinaryRelation.isEquivRel (_≈_ {R = R}) -- {R = _≈_}
weak-delay-isEquivRel = {!!}

delay-set-quotiented-bisim : ∀ R → ∀ (x y : delay R) → (([ x ] ≡ [ y ]) ≡ (x ≈ y))
delay-set-quotiented-bisim R x y = ua (isEquivRel→isEffective {R = _≈_} weak-delay-prop weak-delay-isEquivRel x y)

-- (isEquivRel→isEffective ? ? x y)

--------------
-- Sequence --
--------------

ismon : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → Set
ismon g = (n : ℕ)
  → (g n ≡ g (suc n))
  ⊎ ((g n ≡ inr tt) × ((g (suc n) ≡ inr tt) → ⊥))

Seq : ∀ {A : Set} → Set
Seq {A} = (Σ (ℕ → A ⊎ Unit) ismon)

asda : ∀ (A : Set) (g : ℕ → A ⊎ Unit) (a : ismon g) → ismon {A = A} (λ {0 → inr tt ; (suc n) → g n})
asda A g a 0 = inr {!!}
asda A g a (suc n) = inl {!!}

shift : ∀ {A} → Seq {A} → Seq {A}
shift (g , a) =
  (λ {0 → inr tt ; (suc n) → g n}) ,
  {!!}

-- case g 0 return (λ x → {!!}) of λ x → {!!}

unshift : ∀ {A} → Seq {A} → Seq {A}
unshift (g , a) = g ∘ suc , a ∘ suc

j : ∀ {A} → delay A → Seq {A}
j {A} m = case out-fun m return (λ x → Seq {A}) of
  λ {(inr a , b) → (λ x → inl a) , (λ n → inl refl)
    ;(inl tt , t) → shift (j (t tt))}


-- h : ∀ {A} → Seq {A} → delay A
-- h (g , a) with g 0
-- ... | (inl r) = delay-ret r
-- ... | (inr _) = delay-tau (h (unshift (g , a)))

-- ksd : ∀ {A} b → h {A} (j b) ≡ b
-- ksd b =
--   transport (λ i → h (j (in-inverse-out i b)) ≡ in-inverse-out i b)
--   (case out-fun b return (λ x → h (j (in-fun x)) ≡ in-fun x) of λ {(inr a , c) →
--     h (j (in-fun (inr a , c))) ≡⟨ {!!} ⟩ delay-ret a ≡⟨ {!!} ⟩ in-fun (inr a , c) ∎})

-- delay-is-seq : ∀ {R} → delay R ≡ Seq {R}
-- delay-is-seq = isoToPath (iso j h (λ b → {!!}) {!!})

----------------------
-- Partiality monad --
----------------------

record partiality-monad (A : Set) : Set₁ where
  field
    A⊥ : Set
    _⊑_ : A⊥ → A⊥ → Set

    η : A → A⊥
    ⊥ₐ : A⊥
    ⊔ : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)) → A⊥
    α : (x y : A⊥) → x ⊑ y → y ⊑ x → x ≡ y

    ⊑-refl : ∀ {x : A⊥} → x ⊑ x
    ⊑-trans : ∀ {x y z : A⊥} → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-⊥ : ∀ {x} → ⊥ₐ ⊑ x

    ⊑-prop : isProp ({x y : A⊥} → x ⊑ y)
    ⊑-0 : {(s , p) : Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)} → (n : ℕ) → s n ⊑ ⊔ (s , p)
    ⊑-1 : {(s , p) : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n))} → (x : A⊥) → (n : ℕ) → s n ⊑ x → ⊔ (s , p) ⊑ x

    -- quotient : ∀ x y → x ⊑ y 

open partiality-monad

remove-tau : {!!}

partiality-monad-delay : ∀ {R} → partiality-monad R
A⊥ (partiality-monad-delay {R}) = {!!}
_⊑_ (partiality-monad-delay {R}) x y = {!!}

η (partiality-monad-delay {R}) x = 1 , ((inr x , λ ()) , λ x₁ → inr x , λ ())
⊥ₐ (partiality-monad-delay) = 0 , lift tt , λ x₁ → lift tt -- never
-- ⊔ (partiality-monad-delay) (f , m) = (λ n → f n .fst n) , (λ n → f (suc n) .snd n ∙ cong (λ a → a .fst n) (sym (weak-delay-coinduction (m n))))
-- α (partiality-monad-delay) x y z w = weak-delay-coinduction z

⊑-refl (partiality-monad-delay) = {!!}
⊑-trans (partiality-monad-delay) x y = {!!}
⊑-⊥ (partiality-monad-delay) = {!!} , {!!}

never-x : ∀ {R} n → X (sequence (delay-S R)) n
never-x 0 = lift tt
never-x (suc n) = inl tt , λ _ → never-x n

never-π : ∀ {R} n → π (sequence (delay-S R)) (never-x (suc n)) ≡ never-x n
never-π 0 = refl {x = lift tt}
never-π (suc n) i = inl tt , λ _ → never-π n i

never : ∀ {R} → delay R
never = never-x , never-π
