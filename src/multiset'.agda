{-# OPTIONS --cubical --guardedness #-} --safe

module multiset' where

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

-- open import Cubical.Codata.M.AsLimit.Container
-- open import Cubical.Codata.M.AsLimit.itree
-- open import Cubical.Codata.M.AsLimit.M

open import helper renaming  (rec to rec/)

data T (X : Set) : Set where
  leaf : X → T X
  node : (ℕ → T X) → T X

data _∼T_ {X : Set} : (_ _ : T X) → Set where
  leaf∼ : ∀ (x y : X) → x ≡ y → leaf x ∼T leaf y
  node∼ : {f g : ℕ → T X} → ({n : ℕ} → f n ∼T g n) → node f ∼T node g
  perm∼ : (f : ℕ → T X) (g : ℕ → ℕ) → isEquiv g → node f ∼T node (f ∘ g)

data MS (X : Set) : Set where
    leaf : X → MS X
    node : (ℕ → MS X) → MS X
    perm : (f : ℕ → MS X) → (g : ℕ → ℕ) → isEquiv g → node f ≡ node (f ∘ g)
    MS-isSet : isSet (MS X)

T→MS : ∀ {X} → T X → MS X
T→MS (leaf x) = MS.leaf x
T→MS (node f) = MS.node (T→MS ∘ f)

∼→≡ : {X : Set} {x y : T X} → x ∼T y → T→MS x ≡ T→MS y
∼→≡ (leaf∼ x y p) = cong MS.leaf p
∼→≡ (node∼ f) = cong MS.node (funExt (λ x → ∼→≡ f))
∼→≡ (perm∼ f g e) = perm (T→MS ∘ f) g e

T/∼→MS : {X : Set} → T X / _∼T_ → MS X
T/∼→MS = rec/ T→MS (λ _ _ → ∼→≡) MS-isSet

postulate
  -- leaf≢node : ∀ {f} → leaf ≡ node f → ⊥
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
  
module ElimT
  {X : Set}
  (Tᴹ : MS X → Set)
  (Tset : (x : MS X) → isSet (Tᴹ x))
  (leafᴹ : (x : X) → Tᴹ (leaf x))
  (nodeᴹ : {f : ℕ → MS X} → (fᴹ : (n : ℕ) → Tᴹ (f n)) → Tᴹ (node f))
  (permᴹ : {g : ℕ → MS X} (gᴹ : (n : ℕ) → Tᴹ (g n)) → (f : ℕ → ℕ) (p : isEquiv f)
         → PathP (λ x → Tᴹ (perm g f p x)) (nodeᴹ gᴹ) (nodeᴹ (gᴹ ∘ f))) where
    Elim : (t : MS X) → Tᴹ t
    Elim (leaf x) = leafᴹ x
    Elim (node f) = nodeᴹ (λ n → Elim (f n))
    Elim (perm g f p i) = permᴹ (λ n → Elim (g n)) f p i
    Elim (MS-isSet a b p q i j) =
      isOfHLevel→isOfHLevelDep 2 Tset (Elim a) (Elim b) (cong Elim p) (cong Elim q) (MS-isSet a b p q) i j

T→MS-isSurjection : {X : Set} → Axiom-of-countable-choice ℓ-zero → isSurjection (T→MS {X = X})
T→MS-isSurjection {X = X} acc = ElimT.Elim (λ x → ∥ fiber T→MS x ∥) (λ _ → isProp→isSet propTruncIsProp) leaf-val node-val perm-val
  where
    leaf-val = (λ x → ∣ leaf x , refl ∣)
    
    node-val : {f : ℕ → MS X} → (fᴹ : (n : ℕ) → ∥ fiber T→MS (f n) ∥) → ∥ fiber T→MS (node f) ∥
    node-val = (λ f → ∥map∥ (λ g → (node (fst ∘ g)) , λ i → node (funExt (snd ∘ g) i)) (acc f))

    perm-val : {g : ℕ → MS X} (gᴹ : (n : ℕ) → ∥ fiber T→MS (g n) ∥) → (f : ℕ → ℕ) (p : isEquiv f)
         → PathP (λ x → ∥ fiber T→MS (perm g f p x) ∥) (node-val gᴹ) (node-val (gᴹ ∘ f))
    perm-val {g} gᴹ f p i =
      let temps : ℕ ≡ ℕ
          temps = ua (f , p) in
      let temp : ∥ fiber T→MS (node g) ∥
          temp = ∥map∥ (λ x → node (fst ∘ x) , λ i → node (funExt (snd ∘ x) i)) (acc gᴹ) in
      let tp = perm g f p in
      let temp' = cong (λ j → ∥ fiber T→MS j ∥) (perm g f p) in
      let temps' = ∥map∥ (λ x → ∼→≡ (perm∼ (fst ∘ x) f p) i) (acc gᴹ) in
        {!!}
        -- transport (sym (PathP≡Path (λ x → temp' x) (node-val gᴹ) (node-val (gᴹ ∘ f))))
        -- (subst (λ j → ∥ fiber T→MS j ∥) (perm g f p) (node-val gᴹ)
        --   ≡⟨ {!!} ⟩
        -- node-val (gᴹ ∘ f) ∎)
      
-- T→MS-isSurjection acc (leaf x) = ∣ leaf x , refl ∣
-- T→MS-isSurjection acc (node f) = ∥map∥ (λ {g → (node (fst ∘ g)) , (λ i → node (funExt (snd ∘ g) i))}) (acc (T→MS-isSurjection acc ∘ f))
-- T→MS-isSurjection acc (perm f g e i) = {!!}

T/∼→MS-isSurjection : {X : Set} → Axiom-of-countable-choice ℓ-zero → isSurjection (T/∼→MS {X = X})
T/∼→MS-isSurjection {X = X} acc =
  ElimT.Elim (λ x → ∥ fiber T/∼→MS x ∥) (λ _ → isProp→isSet propTruncIsProp) (leaf-val) node-val perm-val
  where
    leaf-val : (x : X) → ∥ fiber T/∼→MS (leaf x) ∥
    leaf-val x = (∣ [ leaf x ] , refl ∣)

    node-val : {f : ℕ → MS X} → (fᴹ : (n : ℕ) → ∥ fiber T/∼→MS (f n) ∥) → ∥ fiber T/∼→MS (node f) ∥
    node-val {f} f-in =
      Iso.fun double-prop-to-single
      (∥map∥ (λ f' →
       ∥map∥ (λ g →
         ([ node (fst ∘ g) ]) ,
         (node (T/∼→MS ∘ [_] ∘ (fst ∘ g))
           ≡⟨ (λ i → node (T/∼→MS ∘ (funExt (snd ∘ g) i))) ⟩
         node (T/∼→MS ∘ (fst ∘ f'))
           ≡⟨ (λ i → node (funExt (snd ∘ f') i)) ⟩
         node f ∎))
       (acc (λ n → []surjective (fst (f' n)))))
       (acc f-in))

    perm-val : {g : ℕ → MS X} (gᴹ : (n : ℕ) → ∥ fiber T/∼→MS (g n) ∥) → (f : ℕ → ℕ) (p : isEquiv f)
         → PathP (λ x → ∥ fiber T/∼→MS (perm g f p x) ∥) (node-val gᴹ) (node-val (gᴹ ∘ f))
    perm-val {g} gᴹ f p i =
      let temps : ℕ ≡ ℕ
          temps = ua (f , p) in
      let temp : ∥ fiber T/∼→MS (node g) ∥
          temp = raise (∥map∥ (λ x → node (fst ∘ x) , λ i → node (funExt (snd ∘ x) i)) (acc gᴹ)) in
      let tp = perm g f p in
      let temp' = cong (λ j → ∥ fiber T→MS j ∥) (perm g f p) in
      let temps' = {!!} in -- ∥map∥ (λ x → ∼→≡ (perm∼ (fst ∘ x) f p) i) (acc gᴹ) in
        {!!}
        -- transport (sym (PathP≡Path (λ x → temp' x) (node-val gᴹ) (node-val (gᴹ ∘ f))))
        -- (subst (λ j → ∥ fiber T→MS j ∥) (perm g f p) (node-val gᴹ)
        --   ≡⟨ {!!} ⟩
        -- node-val (gᴹ ∘ f) ∎)
      where
        raise = ∥map∥ (λ { (x , y) → [ x ] , y })
      
  
  -- ∥map∥ (λ {(x , y) → [ x ] , y}) (T→MS-isSurjection acc b)


  -- ElimT.Elim
  --   (∥_∥ ∘ fiber T/∼→MS)
  --   ∣ [ bleaf ] , refl ∣
  --   (λ {f} fᴹ →
  --     let temp' = (∥rec∥ propTruncIsProp (idfun ∥ (ℕ → T) ∥)) (∥map∥ (λ x → ∥map∥ (λ x (n : ℕ) → fst (x n)) (acc (λ n → []surjective (x n .fst))) ) (acc fᴹ)) in
  --     let temp = λ (n : ℕ) → (∥rec∥ propTruncIsProp (idfun ∥ MS ∥)) (∥map∥ (λ x → ∥map∥ (T→MS ∘ fst) ([]surjective (x .fst))) (fᴹ n)) in
  --     -- let temp'' : ∣ temp' ∣ ≡ temp
  --     --     temp'' = Iso.leftInv (propTruncIdempotentIso propTruncIsProp) temp
  --     -- in
  --     let temp''' : (n : ℕ) → temp n ≡ ∣ f n ∣
  --         temp''' n = elimProp {A = T} {R = _∼T_}
  --           {B = λ x → (∥map∥ (T→MS ∘ fst) ([]surjective x)) ≡ ∣ f n ∣}
  --           (λ x → isContr→isProp (isProp→isContrPath propTruncIsProp _ _))
  --           (λ x → cong ∣_∣ (T→MS x ≡⟨ {!!} ⟩ f n ∎))
  --           {!!}
  --     in
  --     ∥map∥ (λ x → [ bnode x ] , (node (T→MS ∘ x) ≡⟨ cong node (funExt (λ k → {!!})) ⟩ node f ∎)) temp') -- in [ bnode {!!} ] , {!!} -- (λ x₁ → T→MS (x x₁)) ≡ f
  --   {!!}
  
  -- where
  --   postulate
  --     acc : Axiom-of-countable-choice ℓ-zero
