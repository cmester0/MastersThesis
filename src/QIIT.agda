{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Nat
open import Cubical.Data.Prod

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.SetQuotients

open import Container
open import Coalg
open import itree
open import M
open import stream

open import Cubical.Relation.Binary

module QIIT where

-- Extension / Semantics = P₀ and P₁
-- polynomial functor , which describes strictly positive functors between slice categories of a locally cartesian closed cate-gory

-- A quotient inductive-inductive definition is given by a specification ofits sortsS:Sortsplus a list of constructors, which may be point or pathconstructors, each of which has a sortA2Sand builds upon the categoryof algebras of the previous constructors.

-- The coequalizer coeq π₁, π₂ is the quotient of A by R (bisim relation).

-- effective quotient


record partiality-monad {A : Set} : Set₁ where
  field
    A⊥ : Set
    _⊑_ : A⊥ → A⊥ → Set

    -- set-trunc : (x y : A⊥) (p q : x ≡ y) → p ≡ q

    η : A → A⊥
    ⊥ₐ : A⊥
    ⊔ : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)) → A⊥

    ⊑-refl : ∀ {x : A⊥} → x ⊑ x
    ⊑-trans : ∀ {x y z : A⊥} → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-⊥ : ∀ {x} → ⊥ₐ ⊑ x

    α : (x y : A⊥) → x ⊑ y → y ⊑ x → x ≡ y

    ⊑-prop : isProp ({x y : A⊥} → x ⊑ y)
    ⊑-0 : {(s , p) : Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)} → (n : ℕ) → s n ⊑ ⊔ (s , p)
    ⊑-1 : {(s , p) : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n))} → (x : A⊥) → (n : ℕ) → s n ⊑ x → ⊔ (s , p) ⊑ x

open partiality-monad


delay-to-partiality : ∀ {R} → delay R → {_⊑'_ : R → R → Set} → partiality-monad {R} -- partiality not R ⊎ Unit !
A⊥ (delay-to-partiality {R} a) = delay R
_⊑_ (delay-to-partiality {R} a) = _d⊑_
η (delay-to-partiality {R} a) = delay-ret
⊥ₐ (delay-to-partiality {R} a) = never
⊔ (delay-to-partiality {R} a) = {!!}
⊑-refl (delay-to-partiality {R} a) = {!!}
⊑-trans (delay-to-partiality {R} a) = {!!}
⊑-⊥ (delay-to-partiality {R} a) = {!!}
α (delay-to-partiality {R} a) = {!!}
⊑-prop (delay-to-partiality {R} a) = {!!}
⊑-0 (delay-to-partiality {R} a) = {!!}
⊑-1 (delay-to-partiality {R} a) = {!!}

data _≈_ {R} : (_ _ : delay R) → Set where
  now≈ : ∀ {r : R} → (delay-ret r) ≈ (delay-ret r)
  laterL≈ : ∀ {x y : delay R} → x ≈ y → delay-tau x ≈ y
  laterR≈ : ∀ {x y : delay R} → x ≈ y → x ≈ delay-tau y

weak-prop : ∀ {R} → (a b : delay R) → isProp (a ≈ b)
weak-prop = {!!}

weak-equiv : ∀ {R} → BinaryRelation.isEquivRel (_≈_ {R = R})
weak-equiv = {!!}

effective-weak-bisim : ∀ {R} (a b : delay R) (p : (delay-to-partiality a) ≡ (delay-to-partiality b)) → a ≈ b
effective-weak-bisim a b p =
  {!!}

-- ∀ {R} (x y : delay R) → (delay-to-partiality x) ≡ (delay-to-partiality y) → weak-bisim x y


-- mutual
--   data _d⊑_ {R : Set} : (x y : delay R) → Set where
--     now⊑ :
--       ∀ (x : R) (b : ⊥ → delay R) (y : delay R)
--       → y ↓ x
--       → in-fun (inr x , b) d⊑ y
--     -- now'⊑ : ∀ (x y : R) → x ≡ y → delay-ret x d⊑ delay-ret y
--     later⊑ :
--       ∀ (t u : Unit → delay R)
--       → t tt ∞d⊑ u tt
--       → in-fun (inl tt , t) d⊑ in-fun (inl tt , u)
--     -- never⊑ : ∀ (y : delay R) → y d⊑ never

--   record _∞d⊑_ {R} (x y : delay R) : Set where
--     coinductive
--     field
--       force : x d⊑ y

-- open _∞d⊑_

-- mutual
--   qgjk : ∀ {R} (x : delay R) → x d⊑ x
--   qgjk x =
--     transport (λ i → in-inverse-out i x d⊑ in-inverse-out i x)
--     (case (out-fun x)
--     return (λ x₁ → in-fun x₁ d⊑ in-fun x₁)
--     of λ {(inr r , b) → now⊑ r b (in-fun (inr r , b)) (now↓ r b)
--          ;(inl tt , t) → later⊑ t t (qgjk' (t tt))})

--   qgjk' : ∀ {R} (x : delay R) → x ∞d⊑ x
--   force (qgjk' x) = qgjk x

-- delay-to-partiality : partiality-monad {ℕ}
-- A⊥ (delay-to-partiality) = P₀ {S = delay-S ℕ}(delay ℕ)
-- _⊑_ (delay-to-partiality) x y = in-fun x d⊑ in-fun y
-- -- set-trunc (delay-to-partiality) x y p q = {!!}
-- η (delay-to-partiality) = out-fun ∘ delay-ret
-- ⊥ₐ (delay-to-partiality) = out-fun (delay-ret 0)
-- ⊔ (delay-to-partiality) = λ x → x .fst 0
-- ⊑-refl (delay-to-partiality) = {!!}
-- ⊑-trans (delay-to-partiality) = {!!}
-- ⊑-⊥ (delay-to-partiality) = {!!}
-- α (delay-to-partiality) (inr r , b) (inr s , b') p q = {!!}
-- ⊑-prop (delay-to-partiality) = {!!}
-- ⊑-0 (delay-to-partiality) = {!!}
-- ⊑-1 (delay-to-partiality) = {!!}

-- record simplett {ℓ} : Set (ℓ-suc ℓ) where
--   field
--     Con : Set ℓ
--     Ty : Con → Set ℓ
--     · : Con
--     _▹_ : (Γ : Con) → Ty Γ → Con
--     ι : (Γ : Con) → Ty Γ
--     Σ' : (Γ : Con) → (A : Ty Γ) → Ty (Γ ▹ A) → Ty Γ
--     eq : (Γ : Con) → (A : Ty Γ) → (B : Ty (Γ ▹ A)) → (((Γ ▹ A) ▹ B) ≡ (Γ ▹ (Σ' Γ A B)))

-- open simplett

-- a : ∀ {ℓ} → simplett {ℓ-suc ℓ}
-- Con (a {ℓ}) = Set ℓ
-- Ty (a {ℓ}) = λ x → Set ℓ
-- · (a {ℓ}) = Con (a ℓ}
-- _▹_ a = λ Γ x → {!!}
-- ι a = {!!}
-- Σ' a = {!!}
-- eq a = {!!}

-- a : simplett {ℓ-zero}
-- Con a = stream ℕ
-- Ty a = λ x → ℕ
-- · a = {!!}
-- _▹_ a = λ Γ x → {!!}
-- ι a = {!!}
-- Σ' a = {!!}
-- eq a = {!!}


-- record ssttss {ℓ : Level} : Set (ℓ-suc ℓ) where
--   field
--     Con : Set
--     Ty : Con → Set
--     ε : Con
--     ext : (Γ : Con) → Ty Γ → Con
--     ι : (Γ : Con) → Ty Γ
--     σ : (Γ : Con) → (A : Ty Γ) → Ty (ext Γ A) → Ty Γ
--     σ-eq : (Γ : Con)
--          → (A : Ty Γ)
--          → (B : Ty (ext Γ A))
--          → (ext (ext Γ A) B) ≡ (ext Γ (σ Γ A B))

-- record partiality-monad {ℓ} (R : Set ℓ) : Set (ℓ-suc ℓ) where
--   field
--     Dt : Set ℓ
--     Dnow : R → Dt
--     Dlater : Dt → Dt
--     Rel : Dt → Dt → Set ℓ
--     _∼now_ : ∀ {x : R} → Rel (Dnow x) (Dnow x)
--     _∼laterL_ : ∀ {x y : Dt} → Rel x y → Rel (Dlater x) y
--     _∼laterR_ : ∀ {x y : Dt} → Rel x y → Rel x (Dlater y)
--     te : ∀ {x y : Dt} → Rel x y → x ≡ y

-- mutual
--   data _≈_ {R} : (x y : delay R) → Set where
--     ≈now   : ∀ {r} → delay-ret r ≈ delay-ret r
--     ≈laterL : ∀ {x y} → x ∞≈ y → (delay-tau x) ≈ y
--     ≈laterR : ∀ {x y} → x ∞≈ y → x ≈ (delay-tau y)

--   record _∞≈_ {R} (x y : delay R) : Set where
--     coinductive
--     field
--       force : x ≈ y

-- open _∞≈_

-- sfda : partiality-monad ℕ
-- sfda = record
--          { Dt = delay ℕ
--          ; Dnow = delay-ret
--          ; Dlater = delay-tau
--          ; Rel = _≈_
--          ; _∼now_ = ≈now
--          ; _∼laterL_ = λ {x y} p → ≈laterL (record { force = p })
--          ; _∼laterR_ = λ {x y} p → ≈laterR (record { force = p })
--          ; te = λ p → coinduction _≈_ (record { αᵣ = λ {(a , b , ≈now {r}) → inr r , λ () ; (a , b , ≈laterL {x} {y} p) → inl tt , λ _ → x , y , force p ; (a , b , ≈laterR {x} {y} p) → inl tt , λ _ → x , y , force p} ; rel₁ = λ {i (a , b , ≈now {r}) → out-inverse-in i (inr r , λ ()) ; i (a , b , ≈laterL {x} {y} p) → out-inverse-in i (inl tt , λ _ → x) ; i (a , b , ≈laterR {x} {y} p) → {!!} , {!!}} ; rel₂ = {!!} }) p
--          }
    

-- -- data wq {ℓ} (A C : Set ℓ) (B : A → Set ℓ) (l r : C → A) : Set ℓ where
-- --   point-w :
-- --     (a : A) → (B a → wq A C B l r) → wq A C B l r
-- --   cell-w :
-- --     (c : C) →
-- --     (t : B (l c) → wq A C B l r) →
-- --     (s : B (r c) → wq A C B l r) →
-- --     (point-w (l c) t ≡ point-w (r c) s)

-- -- data mq {ℓ} (S : Container {ℓ}) (C : Set ℓ) (l r : C → S .fst) : Set ℓ where
-- --   point-m :
-- --     (a : S .fst) → (S .snd a → mq S C l r) → mq S C l r
-- --   cell-m :
-- --     (c : C) →
-- --     (t : S .snd (l c) → mq S C l r) →
-- --     (s : S .snd (r c) → mq S C l r) →
-- --     (point-m (l c) t ≡ point-m (r c) s)

-- -- asdkds : ∀ R → mq (delay-S R) (delay R) (λ x → M-coalg .snd x .fst) (λ x → M-coalg .snd (delay-tau x) .fst)
-- -- asdkds R = point-m {!!} {!!}

-- -- mq = M-coalg
-- -- ε (asdkds R) = delay R , ((λ _ → delay R) , (λ e → record { η = delay-tau e ; σ = {!!} }) , λ e → record { η = e ; σ = {!!} })
-- -- qmequ (asdkds R) e ρ = {!!} -- funExt λ x → {!!}

-- -- record T {ℓ} {S : Container {ℓ}} (X : Set ℓ) : Set (ℓ-suc ℓ) where
-- --   coinductive
-- --   field
-- --     η : X
-- --     σ : P₀ {S = S} X
  
-- -- open T

-- -- _>>=_ : ∀ {ℓ} {S : Container {ℓ}} {X Y} -> T {S = S} X → (f : X → Y) → T {S = S} Y
-- -- η (t >>= f) = f (η t)
-- -- σ (t >>= f) = P₁ f (σ t)

-- -- equation-system : ∀ {ℓ : Level} {S : Container {ℓ}} → Set (ℓ-suc ℓ) 
-- -- equation-system {ℓ} {S = S} = Σ (Set ℓ) (λ E → Σ (E → Set ℓ) (λ V → ((e : E) → T {S = S} (V e)) × ((e : E) → T {S = S} (V e)))) -- free V e-coalgebra ?

-- -- sat : ∀ {ℓ} {S : Container {ℓ}} → Coalg₀ {S = S} → equation-system {S = S} → Set (ℓ-suc ℓ)
-- -- sat C,γ (E , V , l , r) = (e : E) → (ρ : V e → C,γ .fst) → ((l e) >>= ρ) ≡ ((r e) >>= ρ)

-- -- record QM-type {ℓ : Level} (S : Container {ℓ}) : Set (ℓ-suc ℓ) where
-- --   field
-- --     QM : Coalg₀ {S = S}
-- --     ε : equation-system
-- --     qmequ : sat QM ε

-- -- open QM-type

-- -- -- This should be a final coalgebra ! (todo add constructors, forcing that, or show this is the case)
-- -- rdgftb : forall R -> (∀ (t : delay R) → t ≡ delay-tau t) -> QM-type (delay-S R)
-- -- QM (rdgftb R h) = M-coalg
-- -- ε (rdgftb R h) = delay R , (λ x → delay R) , (λ e → record { η = e ; σ = M-coalg .snd e }) , λ e → record { η = delay-tau e ; σ = M-coalg .snd e }
-- -- η (qmequ (rdgftb R h) e ρ i) = ρ (h e i)
-- -- σ (qmequ (rdgftb R h) e ρ i) = P₁ ρ (M-coalg .snd e)

-- -- -- Some basic properties of QM-types, the quotiented relation, becomes a bisimulation relation?
-- -- adsgfj : {ℓ : Level} {S : Container {ℓ}} (q : QM-type S) → bisimulation S (QM q) {!!}
-- -- αᵣ (adsgfj q) x = QM q .snd (x .fst) .fst , (λ x₁ → x .fst , x .snd .fst , {!!})
-- -- rel₁ (adsgfj q) = {!!}
-- -- rel₂ (adsgfj q) = {!!}

-- -- -- Basically the construction of the partiality monad, some kinks to work out!

-- -- -- asdkds : ∀ R → QM-type (delay-S R)
-- -- -- QM (asdkds R) = M-coalg
-- -- -- ε (asdkds R) = delay R , ((λ _ → delay R) , (λ e → record { η = delay-tau e ; σ = {!!} }) , λ e → record { η = e ; σ = {!!} })
-- -- -- qmequ (asdkds R) e ρ = {!!} -- funExt λ x → {!!}



-- -- -- record partiality-monad {A : Set} : Set₁ where
-- -- --   field
-- -- --     A⊥ : Set
-- -- --     _⊑_ : A⊥ → A⊥ → Set

-- -- --     η : A → A⊥
-- -- --     ⊥ₐ : A⊥
-- -- --     ⊔ : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)) → A⊥
-- -- --     α : (x y : A⊥) → x ⊑ y → y ⊑ x → x ≡ y

-- -- --     ⊑-refl : ∀ {x : A⊥} → x ⊑ x
-- -- --     ⊑-trans : ∀ {x y z : A⊥} → x ⊑ y → y ⊑ z → x ⊑ z
-- -- --     ⊑-⊥ : ∀ {x} → ⊥ₐ ⊑ x

-- -- --     ⊑-prop : isProp ({x y : A⊥} → x ⊑ y)
-- -- --     ⊑-0 : {(s , p) : Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n)} → (n : ℕ) → s n ⊑ ⊔ (s , p)
-- -- --     ⊑-1 : {(s , p) : (Σ (ℕ → A⊥) λ s → (n : ℕ) → s n ⊑ s (suc n))} → (x : A⊥) → (n : ℕ) → s n ⊑ x → ⊔ (s , p) ⊑ x

-- -- -- open partiality-monad

-- -- -- record partiality-algebra (A : Set) : Set₁ where
-- -- --   field
-- -- --     X : Set
-- -- --     _⊑ₓ_ : X → X → Set
-- -- --     ⊥ₓ : X
-- -- --     ηₓ : A → X
-- -- --     ⊔ₓ : (Σ (ℕ → X) λ s → (n : ℕ) → s n ⊑ₓ s (suc n)) → X

-- -- --     ⊑ₓ-refl : ∀ {x : X} → x ⊑ₓ x
-- -- --     ⊑ₓ-trans : ∀ {x y z : X} → x ⊑ₓ y → y ⊑ₓ z → x ⊑ₓ z
-- -- --     ⊑ₓ-antisym : ∀ {x y : X} → x ⊑ₓ y → y ⊑ₓ x → x ≡ y
-- -- --     ⊑ₓ-⊥ : ∀ {x} → ⊥ₓ ⊑ₓ x

-- -- --     ⊑ₓ-prop : isProp ({x y : X} → x ⊑ₓ y)
-- -- --     ⊑ₓ-0 : ((s , p) : Σ (ℕ → X) λ s → (n : ℕ) → s n ⊑ₓ s (suc n)) → (n : ℕ) → s n ⊑ₓ ⊔ₓ (s , p)
-- -- --     ⊑ₓ-1 : ((s , p) : (Σ (ℕ → X) λ s → (n : ℕ) → s n ⊑ₓ s (suc n))) → (x : X) → (n : ℕ) → s n ⊑ₓ x → ⊔ₓ (s , p) ⊑ₓ x

-- -- -- open partiality-algebra

-- -- -- -- TODO : D(A)/∼D

-- -- -- ω-cpo : Set₁
-- -- -- ω-cpo = partiality-algebra ⊥ 

-- -- -- -- U : ω-cpo → Set
-- -- -- -- U x = X x

-- -- -- postulate
-- -- --   F : Set → ω-cpo

-- -- -- U-partiality-algebra : ∀ x → partiality-algebra ⊥
-- -- -- U-partiality-algebra x = x


