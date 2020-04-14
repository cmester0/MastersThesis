{-# OPTIONS --cubical --guardedness #-} --safe

open import itree
open import M
open import Coalg

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
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
open import Cubical.Foundations.FunExtEquiv

open import Cubical.HITs.SetQuotients

open import Container
open import helper

module bisim-examples where

-------------------------------
-- The identity bisimulation --
-------------------------------

Δ : ∀ {ℓ} {S : Container {ℓ}} -> bisimulation S M-coalg (_≡_)
αᵣ (Δ {S = S}) (a , b , r) = fst (out-fun a) , (λ x → snd (out-fun a) x , (snd (out-fun a) x , refl {x = snd (out-fun a) x}))
rel₁ (Δ {S = S}) = funExt λ {(a , b , r) → refl {x = out-fun a}}
rel₂ (Δ {S = S}) = funExt λ {(a , b , r) → cong (out-fun) (sym r)}

--------------------------------------
-- Bisimulation for the delay monad --
--------------------------------------

mutual
  data Strongly-bisimilar {R} : (x y : delay R) → Set where
    now-cong   : ∀ {r} → Strongly-bisimilar (delay-ret r) (delay-ret r)
    later-cong : ∀ {x y} → ∞Strongly-bisimilar (in-fun (out-fun x)) (in-fun (out-fun y)) → Strongly-bisimilar (delay-tau x) (delay-tau y)

  record ∞Strongly-bisimilar {R} (x y : delay R) : Set where
    coinductive
    field
      force : Strongly-bisimilar x y

open ∞Strongly-bisimilar public

private
  _∼_ = Strongly-bisimilar
  _∞∼_ = ∞Strongly-bisimilar
  
helper-transport : ∀ {R} {x y : delay R} → in-fun (out-fun x) ∼ in-fun (out-fun y) ≡ x ∼ y
helper-transport {x = x} {y} i = in-inverse-out i x ∼ in-inverse-out i y

∞helper-transport : ∀ {R} {x y : delay R} → in-fun (out-fun x) ∞∼ in-fun (out-fun y) ≡ x ∞∼ y
∞helper-transport {x = x} {y} i = in-inverse-out i x ∞∼ in-inverse-out i y

ret-general : ∀ {R} (r : R) (b : ⊥ → delay R) → in-fun (inr r , b) ≡ (delay-ret r)
ret-general r b i = in-fun (inr r , isContr→isProp isContr⊥→A b (λ ()) i)

mutual
  ∞delay≈-refl-helper : ∀ {R} {x : delay R} → in-fun (out-fun x) ∞∼ in-fun (out-fun x)
  force (∞delay≈-refl-helper {x = x}) = delay≈-refl-helper {x = out-fun x}

  delay≈-refl-helper : ∀ {R} {x : P₀ (delay R)} → (in-fun x) ∼ (in-fun x)
  delay≈-refl-helper {x = inr r , b} =
    let temp = (cong (λ a → in-fun (inr r , a)) (isContr→isProp isContr⊥→A (λ ()) b)) in
      transport (λ i → temp i ∼ temp i) now-cong
  delay≈-refl-helper {x = inl tt , t} = later-cong (∞delay≈-refl-helper {x = t tt})

delay≈-refl : ∀ {R} {x : delay R} → x ∼ x
delay≈-refl {x = x} = transport helper-transport (delay≈-refl-helper {x = out-fun x})

later≈ : ∀ {R} {x y : delay R} → in-fun (out-fun x) ∼ in-fun (out-fun y) → delay-tau x ∼ delay-tau y
later≈ p = later-cong (record { force = p })

weak-R-bar : forall {R} -> Set
weak-R-bar {R} = Σ (M (delay-S R)) (λ a → Σ (M (delay-S R)) (_∼_ a))

alpha : forall {R} -> weak-R-bar {R = R} -> P₀ {S = delay-S R} (weak-R-bar {R = R})
alpha (a , b , now-cong {r}) = inr r , λ ()
alpha (a , b , later-cong {x} {y} p) = inl tt , λ _ → x , y , transport helper-transport (force p)

alpha-coalg : ∀ {R} → Coalg₀
alpha-coalg {R} = weak-R-bar {R = R} , alpha

pi : ∀ {R} → (alpha-coalg {R = R}) ⇒ M-coalg
pi = lim-terminal .fst

pi-1 : ∀ {R} → (alpha-coalg {R = R}) ⇒ M-coalg {S = delay-S R}
fst (pi-1) = fst
snd (pi-1) i (a , b , (now-cong {r})) = out-inverse-in i (inr r , λ ())
snd (pi-1 {R}) i (a , b , (later-cong {x} {y} p)) = out-inverse-in i (inl tt , λ _ → x) 

pi-2 : ∀ {R} → (alpha-coalg {R = R}) ⇒ M-coalg
fst (pi-2) = fst ∘ snd
snd (pi-2) i (a , b , (now-cong {r})) = out-inverse-in i (inr r , λ ())
snd (pi-2 {R}) i (a , b , (later-cong {x} {y} p)) = out-inverse-in i (inl tt , λ _ → y)

temp : ∀ {R} → pi-1 ≡ pi-2
temp {R} = final-coalg-property-2 (alpha-coalg {R = R}) M-final-coalg pi-1 pi-2

delay-bisim : ∀ {R} → bisimulation (delay-S R) M-coalg _∼_
delay-bisim = record { αᵣ = alpha ; rel₁ = pi-1 .snd ; rel₂ = pi-2 .snd }

delay-coinduction : ∀ {R} {m m'} → m ∼ m' → m ≡ m'
delay-coinduction {R} = coinduction (_∼_ {R}) delay-bisim
