{-# OPTIONS --cubical --safe #-}
module helper where

open import Cubical.Data.Nat
open import Cubical.Data.Sum renaming (map to ⊎map)
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to empty-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥rec∥ ; elim to ∥elim∥ ; map to ∥map∥)

------------------------
-- Helper definitions --
------------------------

double-prop-to-single : ∀ {ℓ : Level} {A : Type ℓ} → Iso (∥ ∥ A ∥ ∥) (∥ A ∥)
Iso.fun (double-prop-to-single {A = A}) = ∥rec∥ propTruncIsProp (idfun ∥ A ∥)
Iso.inv double-prop-to-single = ∣_∣
Iso.rightInv double-prop-to-single _ = refl
Iso.leftInv double-prop-to-single = ∥elim∥ (λ _ → isProp→isSet propTruncIsProp _ _) (λ _ → refl)

Axiom-of-countable-choice : Type₁
Axiom-of-countable-choice = {B : ℕ → Set} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

isInjective : ∀ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type _
isInjective f = ∀{w x} → f w ≡ f x → w ≡ x

isEmbedding→Injection-x :
  ∀ {ℓ} {A B : Type ℓ}
  → (a : A -> B)
  → (e : isEmbedding a) →
  ----------------------
  ∀ x y → (a x ≡ a y) ≡ (x ≡ y)
isEmbedding→Injection-x a e x y = sym (ua (cong a , e x y))

cancel-inl : {A : Set} {B : Set} {x y : A} → _≡_ {A = A ⊎ B} (inl x) (inl y) → x ≡ y
cancel-inl {A} {B} {x = x} = λ p i → case p i of λ {(inl y) → const y x ; (inr y) → idfun A x}

cancel-inr : {A : Set} {B : Set} {x y : B} → _≡_ {A = A ⊎ B} (inr x) (inr y) → x ≡ y
cancel-inr {A} {B} {x = x} = λ p i → case p i of λ { (inr y) → const y x ; (inl y) → idfun B x }

inl≢inr : ∀ {A : Set} {B : Set} → {x : A} {y : B} → inl x ≡ inr y → ⊥
inl≢inr {A = A} {B} x = subst (λ {(inl x) → A ⊎ B ; (inr y) → ⊥}) x (x i0)

-- Quotient recursor
rec :
  ∀ {ℓ} {A B : Type ℓ} {R : A → A → Type ℓ}
  → (f : A → B)
  → (∀ x y → R x y → f x ≡ f y)
  → isSet B
  → A / R → B
rec {A = A} {B} {R} f feq B-set x = rec' x
 where
   rec' : A / R → B
   rec' [ x ] = f x
   rec' (eq/ a b r i) = feq a b r i
   rec' (squash/ a b p q i j) = B-set (rec' a) (rec' b) (cong rec' p) (cong rec' q) i j

A-Unit-set : ∀ {A : Set} → isSet A → isSet (A ⊎ Unit)
A-Unit-set A-set (inl r) (inl a) p q =
  let temp = (A-set r a (transport (isEmbedding→Injection-x inl isEmbedding-inl r a) p) (transport (isEmbedding→Injection-x inl isEmbedding-inl r a) q)) in
  let temp' = transport (isEmbedding→Injection-x inl isEmbedding-inl r a) p ≡
              transport (isEmbedding→Injection-x inl isEmbedding-inl r a) q
                ≡⟨ isEmbedding→Injection-x (transport (isEmbedding→Injection-x inl isEmbedding-inl r a)) (iso→isEmbedding (pathToIso (isEmbedding→Injection-x inl isEmbedding-inl r a))) p q ⟩
              p ≡ q ∎
  in transport temp' temp
A-Unit-set A-set (inl r) (inr tt) p q = empty-rec (inl≢inr p)
A-Unit-set A-set (inr tt) (inl b) p q = empty-rec (inl≢inr (sym p))
A-Unit-set A-set (inr tt) (inr tt) p q =
  let temp = (isProp→isSet (isContr→isProp (tt , (λ y i → tt)))) in
  let temp' = (temp tt tt (transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt) p) (transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt) q)) in
  let temp'' = transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt) p ≡
               transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt) q
                 ≡⟨ isEmbedding→Injection-x (transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt)) (iso→isEmbedding (pathToIso (isEmbedding→Injection-x inr isEmbedding-inr tt tt))) p q ⟩
               p ≡ q ∎
  in
  transport temp'' temp'


-- Natural number ordering (≤ and <)
module _ where
  open import Cubical.Data.Nat.Order

  ≰→> : ∀ {m n} → (m ≤ n → ⊥) → n < m
  ≰→> {zero} {n} p = Cubical.Data.Empty.elim (p (zero-≤))
  ≰→> {suc m} {zero}  p = suc-≤-suc (zero-≤)
  ≰→> {suc m} {suc n} p = suc-≤-suc (≰→> (p ∘ suc-≤-suc))

  Dec : ∀ {p} → Set p → Set p
  Dec P = P ⊎ (P → ⊥)

  Decidable :
    ∀ {a b ℓ} {A : Set a} {B : Set b}
    → (A → B → Set ℓ)
    → Set (ℓ-max (ℓ-max a b) ℓ)
  Decidable _∼_ = ∀ x y → Dec (x ∼ y)

  _≤?_ : Decidable _≤_
  zero  ≤? n     = inl (zero-≤)
  suc m ≤? zero  = inr λ { x → ¬-<-zero x }
  suc m ≤? suc n = ⊎map suc-≤-suc (λ m≰n → m≰n ∘ pred-≤-pred) (m ≤? n)

  ≤⊎> : ∀ m n → (m ≤ n) ⊎ (n < m)
  ≤⊎> m n = ⊎map (idfun (Σ ℕ (λ z → z + m ≡ n))) ≰→> (m ≤? n)

  total : ∀ m n → (m ≤ n) ⊎ (n ≤ m)
  total m n = Cubical.Data.Sum.map (idfun (Σ ℕ (λ z → z + m ≡ n))) ≰→≥ (m ≤? n)
    where
      ≰→≥ : ∀ {m n} → (m ≤ n → ⊥) → n ≤ m
      ≰→≥ p = ≤-trans (≤-suc ≤-refl) (≰→> p)


