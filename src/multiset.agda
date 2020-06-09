{-# OPTIONS --cubical --guardedness #-} --safe

module multiset where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to empty-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥ ; elim to ∥elim∥ ; rec to ∥rec∥)
open import Cubical.HITs.SetQuotients

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv

open import helper renaming  (rec to rec/)

data T (X : Set) : Set where
  leaf : X → T X
  node : (ℕ → T X) → T X

data _∼T_ {X : Set} : (_ _ : T X) → Set where
  leaf∼ : ∀ (x y : X) → x ≡ y → leaf x ∼T leaf y
  node∼ : {f g : ℕ → T X} → ({n : ℕ} → f n ∼T g n) → node f ∼T node g
  perm∼ : (f : ℕ → T X) (ge : ℕ ≃ ℕ) → node f ∼T node (f ∘ ge .fst)

data MS (X : Set) : Set where
    leaf : X → MS X
    node : (ℕ → MS X) → MS X
    perm : (f : ℕ → MS X) → (ge : ℕ ≃ ℕ) → node f ≡ node (f ∘ ge .fst)
    MS-isSet : isSet (MS X)

T→MS : ∀ {X} → T X → MS X
T→MS (leaf x) = MS.leaf x
T→MS (node f) = MS.node (T→MS ∘ f)

∼→≡ : {X : Set} {x y : T X} → x ∼T y → T→MS x ≡ T→MS y
∼→≡ (leaf∼ x y p) = cong MS.leaf p
∼→≡ (node∼ f) = cong MS.node (funExt (λ x → ∼→≡ f))
∼→≡ (perm∼ f (g , e)) = perm (T→MS ∘ f) (g , e)

T/∼→MS : {X : Set} → T X / _∼T_ → MS X
T/∼→MS = rec/ T→MS (λ _ _ → ∼→≡) MS-isSet

postulate
  leaf≢node : ∀ {X : Set} {x : X} {f} → MS.leaf x ≡ MS.node f → ⊥
  nodeIsInjective : ∀ {X : Set} → isInjective (MS.node {X = X})
  leafIsInjective : ∀ {X : Set} → isInjective (MS.leaf {X = X})

≡→∼ : {X : Set} {x y : T X} → T→MS x ≡ T→MS y → x ∼T y
≡→∼ {x = leaf x} {y = leaf y} p = leaf∼ x y (leafIsInjective p)
≡→∼ {x = leaf x} {y = node g} p = empty-rec (leaf≢node p)
≡→∼ {x = node f} {y = leaf y} p = empty-rec (leaf≢node (sym p))
≡→∼ {x = node f} {y = node g} p =
  node∼ λ {n} → ≡→∼ (Iso.inv funExtIso (nodeIsInjective p) n)

T/∼→MS-isInjective : {X : Set} → isInjective T/∼→MS
T/∼→MS-isInjective {X} {x} {y} =
  elimProp
    {A = T X}
    {R = _∼T_}
    {B = λ x → T/∼→MS x ≡ T/∼→MS y → x ≡ y}
    (λ x → isPropΠ λ _ → squash/ x y)
    (λ x →
      elimProp
      {A = T X}
      {R = _∼T_}
      {B = λ y → T/∼→MS [ x ] ≡ T/∼→MS y → [ x ] ≡ y}
      (λ y → isPropΠ λ _ → squash/ [ x ] y)
      (λ y → eq/ x y ∘ ≡→∼)
      y)
    x

{-# NON_TERMINATING #-}
elimPropMS : {X : Set} (P : MS X → Set) (Pprop : (x : MS X) → isProp (P x)) (Pleaf : (x : X) → P (leaf x)) (Pnode : {f : ℕ → MS X} → (f' : (n : ℕ) → P (f n)) → P (node f)) (t : MS X) → P t
elimPropMS {X} P Pprop Pleaf Pnode = temp
  where
    temp : (t : MS X) → P t
    temp (leaf x) = Pleaf x
    temp (node f) = Pnode (λ n → temp (f n))
    temp (perm g e i) =
      isOfHLevel→isOfHLevelDep 1 Pprop (temp (node g)) (temp (node (g ∘ (e .fst)))) (perm g e) i  -- problem here
    temp (MS-isSet a b p q i j) =
      isOfHLevel→isOfHLevelDep 2 (isProp→isSet ∘ Pprop) (temp a) (temp b) (cong temp p) (cong temp q) (MS-isSet a b p q) i j
  
T→MS-isSurjection : {X : Set} → Axiom-of-countable-choice ℓ-zero → isSurjection (T→MS {X = X})
T→MS-isSurjection {X = X} acc = elimPropMS (λ x → ∥ fiber T→MS x ∥) (λ _ → propTruncIsProp) leaf-val node-val
  where
    leaf-val : (x : X) → ∥ fiber T→MS (leaf x) ∥
    leaf-val x = ∣ leaf x , refl ∣
    
    node-val : {f : ℕ → MS X} → (fᴹ : (n : ℕ) → ∥ fiber T→MS (f n) ∥) → ∥ fiber T→MS (node f) ∥
    node-val = ∥map∥ (λ g → (node (fst ∘ g)) , λ i → node (funExt (snd ∘ g) i)) ∘ acc

T/∼→MS-isSurjection : {X : Set} → Axiom-of-countable-choice ℓ-zero → isSurjection (T/∼→MS {X = X})
T/∼→MS-isSurjection {X = X} acc = ∥map∥ (λ {(x , y) → [ x ] , y}) ∘ (T→MS-isSurjection acc)
