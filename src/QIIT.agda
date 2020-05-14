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

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.Coalg
open import Cubical.Codata.M.AsLimit.M

open import Cubical.Relation.Binary

module QIIT where

-- Extension / Semantics = P₀ and P₁
-- polynomial functor , which describes strictly positive functors between slice categories of a locally cartesian closed cate-gory

-- A quotient inductive-inductive definition is given by a specification ofits sortsS:Sortsplus a list of constructors, which may be point or pathconstructors, each of which has a sortA2Sand builds upon the categoryof algebras of the previous constructors.

-- The coequalizer coeq π₁, π₂ is the quotient of A by R (bisim relation).

-- effective quotient

---------------------------------------------------------
-- Quotients defined by containers? (Partiality monad) --
---------------------------------------------------------

delay-helper : ∀ (R : Set) → (R ⊎ Unit) → Set
delay-helper R (inl _) = ⊥
delay-helper R (inr tt) = Unit

-- itrees (and buildup examples)
delay-S : (R : Set₀) -> Container ℓ-zero
delay-S R = (R ⊎ Unit ) , delay-helper R

delay : (R : Set₀) -> Set₀
delay R = M (delay-S R)

-- ret = now
delay-ret : {R : Set} -> R -> delay R
delay-ret r = in-fun (inl r , λ ())

-- tau = later
delay-tau : {R : Set₀} -> delay R -> delay R
delay-tau t = in-fun (inr tt , λ _ → t)

mutual
  data _≈_ {R} : (x y : delay R) → Set where
    ≈now : ∀ {x : R} → delay-ret x ≈ delay-ret x
    ≈later : ∀ {x y : delay R} → x ∞≈ y → (delay-tau x) ≈ (delay-tau y)
    ≈laterˡ : ∀ {x y : delay R} → x ≈ y → (delay-tau x) ≈ y
    ≈laterʳ : ∀ {x y : delay R} → x ≈ y → x ≈ (delay-tau y)

  record _∞≈_ {R} (x y : delay R) : Set where
    coinductive
    field
      force : x ≈ y

open _∞≈_

asfg : ∀ (R : Type₀) → Container ℓ-zero
asfg R = delay R , λ x → Σ[ y ∈ delay R ] x ≈ y

partiality : ∀ (R : Type₀) → Type₀
partiality R = M (asfg R)

ash : ∀ R → partiality R → delay R / _≈_
ash R p = [ out-fun p .fst ]

lift-val : ∀ {R} → delay R → partiality R
lift-val {R} x = in-fun (x , λ _ → lift-direct-M lift-x lift-π)
  where
    lift-x : (n : ℕ) → Wₙ (asfg R) n
    lift-x 0 = lift tt
    lift-x (suc n) = x , λ _ → lift-x n
    
    lift-π : (n : ℕ) → πₙ (asfg R) (lift-x (suc n)) ≡ lift-x n
    lift-π 0 = refl
    lift-π (suc n) i = x , (λ _ → lift-π n i)

ash' : ∀ R → delay R / _≈_ → partiality R
ash' R [ p ] = lift-val p
ash' R (eq/ x y p i) = cong (ash' R) (eq/ x y p) i
ash' R (squash/ x y p q i j) = cong (ash' R) (squash/ x y p q i) j
