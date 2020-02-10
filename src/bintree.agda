{-# OPTIONS --cubical --guardedness --safe --copatterns #-}  

module bintree where

  open import Cubical.Foundations.Everything
  open import Cubical.Core.Everything

  open import Cubical.Data.Nat as ℕ using (ℕ)
  open import Cubical.Data.Unit
  open import Cubical.Data.Bool

  open import Cubical.Codata.M

  -- Type
  bintree : Set -> Set
  bintree A = M ((λ {tt → A}) , λ {tt x tt → Bool}) tt   -- x : A 

  -- Definitions
  bintree-value : ∀ {A} -> bintree A -> A
  bintree-value t = t .head
  
  bintree-left : ∀ {A} -> bintree A -> bintree A
  bintree-left t = t .tails tt false -- out tt t .snd tt false
  
  bintree-right : ∀ {A} -> bintree A -> bintree A
  bintree-right t = t .tails tt true -- out tt t .snd tt true

  -- Bisimulation
  record _≈_ {A : Type₀} (x y : bintree A) : Type₀ where
    coinductive
    field
      ≈value : bintree-value x ≡ bintree-value y
      ≈left :  bintree-left x  ≈ bintree-left y
      ≈right : bintree-right x ≈ bintree-right y

  open _≈_

  if : ∀ {ℓ} {A : Type ℓ} -> Bool -> A -> A -> A
  if true x _ = x
  if false _ y = y

  bisim : {A : Type₀} → {x y : bintree A} → x ≈ y → x ≡ y
  head  (bisim x≈y i)          = ≈value x≈y i
  tails (bisim x≈y i) tt false = bisim (≈left x≈y) i
  tails (bisim x≈y i) tt true  = bisim (≈right x≈y) i
  
  misib : {A : Type₀} → {x y : bintree A} → x ≡ y → x ≈ y
  ≈value (misib p) =        λ i → bintree-value (p i)
  ≈left  (misib p) = misib (λ i → bintree-left  (p i))
  ≈right (misib p) = misib (λ i → bintree-right (p i))

  iso1 : {A : Type₀} → {x y : bintree A} → (p : x ≡ y) → bisim (misib p) ≡ p
  head  (iso1 p i j)          = bintree-value (p j)
  tails (iso1 p i j) tt false = iso1 (λ i → bintree-left  (p i)) i j
  tails (iso1 p i j) tt true  = iso1 (λ i → bintree-right (p i)) i j
  
  iso2 : {A : Type₀} → {x y : bintree A} → (p : x ≈ y) → misib (bisim p) ≡ p
  ≈value (iso2 p i) = ≈value p
  ≈left  (iso2 p i) = iso2 (≈left p) i
  ≈right (iso2 p i) = iso2 (≈right p) i
  
  path≃bisim : {A : Type₀} → {x y : bintree A} → (x ≡ y) ≃ (x ≈ y)
  path≃bisim = isoToEquiv (iso misib bisim iso2 iso1)

  path≡bisim : {A : Type₀} → {x y : bintree A} → (x ≡ y) ≡ (x ≈ y)
  path≡bisim = ua path≃bisim

  -- Examples
  nat-bintree' : ∀ k -> bintree ℕ
  nat-bintree' k .head = ℕ.predℕ k
  nat-bintree' k .tails = λ { y false -> nat-bintree'        (2 ℕ.* k) 
                            ; y true ->  nat-bintree' (ℕ.suc (2 ℕ.* k)) }

  nat-bintree = nat-bintree' 1

  mapT : ∀ {A B} -> (A -> B) -> bintree A -> bintree B
  head  (mapT f s)          = f (bintree-value s)
  tails (mapT f s) tt false = mapT f (bintree-left s)
  tails (mapT f s) tt true  = mapT f (bintree-right s)
  
  open import stream using (stream ; stream-nth ; nat-stream)

  -- tree-to-stream : ∀ {A} -> bintree A -> stream A
  -- tree-to-stream t = mapS index nat-stream 

  stream-to-tree : ∀ {A} -> stream A -> bintree A
  stream-to-tree s = mapT (λ n -> stream-nth n s) nat-bintree

  asdfasdf : stream-to-tree nat-stream ≈ nat-bintree
  ≈value asdfasdf = refl
  ≈left asdfasdf = {!!}
  ≈right asdfasdf = {!!}
