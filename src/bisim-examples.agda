{-# OPTIONS --cubical --guardedness #-} --safe
module bisim-examples where

open import itree
open import M
open import Coalg
open import QPF

open import Cubical.Data.Unit
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Cubical.Codata.Stream
-- open import Agda.Builtin.Coinduction
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.HITs.SetQuotients

---------------------------------
-- Quotienting the delay monad --
---------------------------------

data delay≈ {R} : (delay R) -> (delay R) -> Set where
  EqPNow : ∀ r s -> r ≡ s -> delay≈ (delay-ret r) (delay-ret s)
  EqPLater : ∀ t u -> delay≈ t u -> delay≈ (delay-tau t) (delay-tau u)

data weak-delay≈ {R} : (delay R) -> (delay R) -> Set where
  EqNow : ∀ {r s} -> r ≡ s -> weak-delay≈ (delay-ret r) (delay-ret s)
  EqLater : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) (delay-tau u)
  EqLaterL : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) u
  EqLaterR : ∀ {t u} -> weak-delay≈ t u -> weak-delay≈ t (delay-tau u)

-- isEmbedding -- TODO!

Qdelay : ∀ {R} -> delay R -> QM (weak-delay≈)
Qdelay = [_]

-- constant step delayed and non Delayed programs are equal
delay-once : Qdelay (delay-tau (delay-ret 2)) ≡ Qdelay (delay-ret 2)
delay-once = λ i → eq/ (delay-tau (delay-ret 2)) (delay-ret 2) (EqLaterL (EqNow refl)) i

Qdelay-Container : ∀ {R : Set} -> Container {ℓ-zero}
Qdelay-Container {R} = delay R / weak-delay≈ , {!!} -- delay R / weak-delay≈ , λ { [ x ] -> case out-fun x of λ (x₁ , b) → {!!} }

Qdelay-type : ∀ {R : Set} -> Set
Qdelay-type {R = R} = M (Qdelay-Container {R = R})

asdff : ∀ {R : Set} -> R -> Qdelay-type {R = R}
asdff {R} r = in-fun {S = Qdelay-Container {R = R}} ( [ delay-ret r ] , λ x → {!!})

-- asdf' : ∀ {R} -> bisimulation (delay-S R) M-coalg delay≈
-- αᵣ asdf' = {!!}
-- rel₁ (asdf' {R = R}) i ((a , c) , b , EqPNow r s p) = {!!}
-- rel₁ (asdf' {R = R}) i (a , b , EqPLater _ _ _) = {!!}
-- rel₂ asdf' = {!!}

data itree≈ {E} {R} : itree E R -> itree E R -> Set₁ where
  EqRet : ∀ r s -> r ≡ s -> itree≈ (ret r) (ret s)
  EqTau : ∀ t u -> itree≈ t u -> itree≈ (tau t) (tau u)
  EqVis : ∀ {A} e k1 k2 -> k1 ≡ k2 -> itree≈ (vis {A = A} e k1) (vis {A = A} e k2)

open itree≈

-- ((Unit ⊎ R) ⊎ Σ Set E) -,- (λ { (inl (inl _)) -> Lift Unit ; (inl (inr _)) -> ⊥₁ ; (inr (A , e)) -> Lift A } )
itree-bisim : ∀ {E : Set₀ -> Set₁} {R : Set₀} -> bisimulation (itree-S E R) M-coalg itree≈
αᵣ (itree-bisim {E} {R}) = {!!}
rel₁ itree-bisim = λ i → λ a → {!!}
rel₂ itree-bisim = {!!}

-- spin≡spin : ∀ {R} -> spin {R} ≡ spin
-- spin≡spin {R = R} = coinduction (delay-S R) delay-bisim spin spin (delay-tau≈ spin spin {!!})
