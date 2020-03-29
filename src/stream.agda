{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Transport

-- open import Cubical.Codata.Stream

open import M
open import helper
open import Container
open import Container-M-type

open import Cubical.Foundations.Embedding

module stream where

--------------------------------------
-- Stream definitions using M-types --
--------------------------------------

stream-S : ∀ {ℓ} (A : Set ℓ) -> Container {ℓ}
stream-S A = (A , (λ _ → Lift Unit))

stream : ∀ {ℓ} (A : Set ℓ) -> Set ℓ
stream A = M (stream-S A)

cons : ∀ {ℓ} {A : Set ℓ} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { (lift tt) -> xs } )

hd : ∀ {ℓ} {A : Set ℓ} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {ℓ} {A : Set ℓ} -> stream A -> stream A
tl {A} S = out-fun S .snd (lift tt)

open isEquiv

-- hd-isEmbedding : ∀ {A} → isEmbedding (hd {A = A})
-- fst (fst (equiv-proof (hd-isEmbedding {A} w z) y)) =
--   {!!}
--      ≡⟨ {!!} ⟩
--   {!!} ∎
-- snd (fst (equiv-proof (hd-isEmbedding {A} w z) y)) = {!!}
-- snd (equiv-proof (hd-isEmbedding {A} w z) y) = {!!}

--------------------
-- Cons-injective --
--------------------

cons-inj : ∀ {ℓ} {A : Set ℓ} (x : A) (xs : stream A) (y : A) (ys : stream A) → (cons x xs ≡ cons y ys) ≡ (x ≡ y) × (xs ≡ ys)
cons-inj x xs y ys =
  cons x xs ≡ cons y ys
     ≡⟨ in-inj-x ⟩
  (x , λ {(lift tt) → xs}) ≡ (y , λ {(lift tt) → ys})
     ≡⟨ sym Σ-split ⟩
  (x ≡ y) ×Σ ((λ { (lift tt) → xs }) ≡ (λ { (lift tt) → ys }))
     ≡⟨ cong (λ a → (x ≡ y) ×Σ a) (isoToPath (iso (λ a → funExt⁻ a (lift tt))
                                                    (λ a → cong (λ b → λ {(lift tt) → b}) a)
                                                    (λ b → refl)
                                                    (λ a → refl))) ⟩
  (x ≡ y) ×Σ (xs ≡ ys)
     ≡⟨ sym A×B≡A×ΣB ⟩
  (x ≡ y) × (xs ≡ ys) ∎

-- -------------------------------
-- -- Expanding stream equality --
-- -------------------------------

-- stream-expand-2 : ∀ {ℓ} {A : Set ℓ} {s t : stream A} → (s ≡ t) ≡ (cons (hd s) (tl s) ≡ cons (hd t) (tl t))
-- stream-expand-2 = sym in-out-id

-- stream-expand-1 : ∀ {ℓ} {A : Set ℓ} {a c : A} {b d : stream A} → (cons a b ≡ cons c d) ≡ (a ≡ c) × (b ≡ d)
-- stream-expand-1 {a = a} {c} {b} {d} =
--   (cons a b ≡ cons c d)
--     ≡⟨ in-inj-x ⟩
--   ((a , (λ { (lift tt) → b })) ≡ (c , (λ { (lift tt) → d })))
--     ≡⟨ sym Σ-split-iso ⟩
--   (Σ (a ≡ c) (λ _ → (λ { (lift tt) → b }) ≡ λ { (lift tt) → d }))
--      ≡⟨ isoToPath (iso (λ {(x , y) → x , funExt⁻ y (lift tt)}) (λ {(x , y) → x , funExt (λ { (lift tt) → y})}) (λ b₁ → refl) λ a₁ → refl) ⟩
--   (Σ (a ≡ c) (λ _ → b ≡ d))
--      ≡⟨ sym A×B≡A×ΣB ⟩
--   ((a ≡ c) × (b ≡ d)) ∎

-- stream-expand : ∀ {ℓ} (A : Set ℓ) (s t : stream A) → (s ≡ t) ≡ (hd s ≡ hd t) × (tl s ≡ tl t)
-- stream-expand A s t = stream-expand-2 □ stream-expand-1

-- postulate
--   stream-cons-expand : ∀ {ℓ} {A : Set ℓ} (s : stream A) → s ≡ (cons (hd s) (tl s))

-- hd-is-hd : ∀ {ℓ} (A : Set ℓ) (x : A) (xs : stream A) → hd (cons x xs) ≡ x
-- hd-is-hd A x xs =
--   hd (cons x xs)
--     ≡⟨ refl ⟩
--   hd (in-fun (x , λ { (lift tt) → xs }))
--     ≡⟨ refl ⟩
--   out-fun (in-fun (x , λ { (lift tt) → xs })) .fst
--     ≡⟨ (λ i → out-inverse-in {S = stream-S A} i (x , λ { (lift tt) → xs }) .fst) ⟩
--   x ∎

-- tl-is-tl : ∀ {ℓ} (A : Set ℓ) (x : A) (xs : stream A) → tl (cons x xs) ≡ xs
-- tl-is-tl A x xs =
--   tl (cons x xs)
--     ≡⟨ refl ⟩
--   tl (in-fun (x , λ { (lift tt) → xs }))
--     ≡⟨ refl ⟩
--   out-fun (in-fun (x , λ { (lift tt) → xs })) .snd (lift tt)
--     ≡⟨ (λ i → out-inverse-in {S = stream-S A} i (x , λ { (lift tt) → xs }) .snd (lift tt)) ⟩
--   xs ∎

-- --------------------------
-- -- Stream using M-types --
-- --------------------------

-- stream-pair-M : ∀ {ℓ} (A B : Set ℓ) → stream A × stream B ≡ M (Container-product (stream-S A) (stream-S B))
-- stream-pair-M A B = M-product-equality (stream-S A) (stream-S B)

-- Container-product-streams : ∀ {ℓ} (A B : Set ℓ) → Container-product (stream-S A) (stream-S B) ≡ stream-S (A × B)
-- Container-product-streams A B =
--   Container-product (stream-S A) (stream-S B)
--     ≡⟨ refl ⟩
--   (A × B , λ x → Lift Unit × Lift Unit )
--     ≡⟨ (λ i → (A × B) , λ _ → sym diagonal-unit i) ⟩
--   (A × B , λ x → Lift Unit )
--     ≡⟨ refl ⟩
--   stream-S (A × B) ∎

-- stream-pair : ∀ {ℓ} (A B : Set ℓ) → stream A × stream B ≡ stream (A × B)
-- stream-pair A B = stream-pair-M A B □ λ i → M (Container-product-streams A B i)

-- zip : ∀ {ℓ} {A B : Set ℓ} → stream A × stream B → stream (A × B)
-- zip {A = A} {B} = transport (stream-pair A B)

-- ------------------------
-- -- Record stream type --
-- ------------------------

-- record Stream {ℓ} (A : Set ℓ) : Set ℓ where
--   coinductive
--   constructor _,_
--   field
--     head : A
--     tail : Stream A

-- open Stream

-- -- Bisimulation
-- record _≈_ {ℓ} {A : Set ℓ} (x y : Stream A) : Set ℓ where
--   coinductive
--   field
--     ≈head : head x ≡ head y
--     ≈tail : tail x ≈ tail y

-- open _≈_

-- bisim : ∀ {ℓ} {A : Set ℓ} → {x y : Stream A} → x ≈ y → x ≡ y
-- head (bisim x≈y i) = ≈head x≈y i
-- tail (bisim x≈y i) = bisim (≈tail x≈y) i

-- misib : ∀ {ℓ} {A : Set ℓ} → {x y : Stream A} → x ≡ y → x ≈ y
-- ≈head (misib p) = λ i → head (p i)
-- ≈tail (misib p) = misib (λ i → tail (p i))

-- iso1 : ∀ {ℓ} {A : Set ℓ} → {x y : Stream A} → (p : x ≡ y) → bisim (misib p) ≡ p
-- head (iso1 p i j) = head (p j)
-- tail (iso1 p i j) = iso1 (λ i → tail (p i)) i j

-- iso2 : ∀ {ℓ} {A : Set ℓ} → {x y : Stream A} → (p : x ≈ y) → misib (bisim p) ≡ p
-- ≈head (iso2 p i) = ≈head p
-- ≈tail (iso2 p i) = iso2 (≈tail p) i

-- path≃bisim : ∀ {ℓ} {A : Set ℓ} → {x y : Stream A} → (x ≡ y) ≃ (x ≈ y)
-- path≃bisim = isoToEquiv (iso misib bisim iso2 iso1)

-- path≡bisim : ∀ {ℓ} {A : Set ℓ} → {x y : Stream A} → (x ≡ y) ≡ (x ≈ y)
-- path≡bisim = ua path≃bisim

-- ------------------------------
-- -- Equality of stream types --
-- ------------------------------

-- stream-to-Stream : ∀ {ℓ} {A : Set ℓ} → stream A → Stream A
-- head (stream-to-Stream x) = (hd x)
-- tail (stream-to-Stream x) = (stream-to-Stream (tl x))

-- Stream-to-stream-func-x : ∀ {ℓ} {A : Set ℓ} (n : ℕ) -> Stream A → X (sequence (stream-S A)) n
-- Stream-to-stream-func-x 0 x = lift tt
-- Stream-to-stream-func-x (suc n) x = head x , λ x₁ → Stream-to-stream-func-x n (tail x)

-- Stream-to-stream-func-π : ∀ {ℓ} {A : Set ℓ} (n : ℕ) (a : Stream A) → π (sequence (stream-S A)) (Stream-to-stream-func-x (suc n) a) ≡ Stream-to-stream-func-x n a
-- Stream-to-stream-func-π 0 a = refl
-- Stream-to-stream-func-π (suc n) a = λ i → head a , λ _ → Stream-to-stream-func-π n (tail a) i

-- Stream-to-stream : ∀ {ℓ} {A : Set ℓ} -> Stream A -> stream A
-- Stream-to-stream s = lift-to-M Stream-to-stream-func-x Stream-to-stream-func-π s

-- postulate
--   head-to-hd : ∀ {ℓ} {A : Set ℓ} (b : stream A) → head (stream-to-Stream b) ≡ hd b
--   hd-to-head : ∀ {ℓ} {A : Set ℓ} (b : Stream A) → hd (Stream-to-stream b) ≡ head b
--   tail-to-tl : ∀ {ℓ} {A : Set ℓ} (b : stream A) → tail (stream-to-Stream b) ≡ stream-to-Stream (tl b)
--   tl-to-tail : ∀ {ℓ} {A : Set ℓ} (b : Stream A) → tl (Stream-to-stream b) ≡ Stream-to-stream (tail b)

-- nth : ∀ {ℓ} {A : Set ℓ} → ℕ → (b : Stream A) → A
-- nth 0 b = head b
-- nth (suc n) b = nth n (tail b)

-- helper : ∀ {ℓ} {A : Set ℓ} → (b : Stream A) → ((n : ℕ) → nth n (stream-to-Stream (Stream-to-stream b)) ≡ nth n b)
-- helper b 0 = head-to-hd (Stream-to-stream b) □ hd-to-head b
-- helper b (suc n) =
--   nth (suc n) (stream-to-Stream (Stream-to-stream b))
--     ≡⟨ refl ⟩
--   nth n (tail (stream-to-Stream (Stream-to-stream b)))
--     ≡⟨ cong (nth n) (tail-to-tl (Stream-to-stream b) □ cong stream-to-Stream (tl-to-tail b)) ⟩
--   nth n (stream-to-Stream (Stream-to-stream (tail b)))
--     ≡⟨ helper (tail b) n ⟩
--   nth n (tail b) ∎

-- bisim-nat' : ∀ {ℓ} {A : Set ℓ} → (a b : Stream A) → ((n : ℕ) → nth n a ≡ nth n b) -> a ≈ b
-- ≈head (bisim-nat' a b nat-bisim) = nat-bisim 0
-- ≈tail (bisim-nat' a b nat-bisim) = bisim-nat' (tail a) (tail b) (nat-bisim ∘ suc)

-- bisim-nat : ∀ {ℓ} {A : Set ℓ} → (a b : Stream A) → ((n : ℕ) → nth n a ≡ nth n b) -> a ≡ b
-- bisim-nat a b nat-bisim = bisim (bisim-nat' a b nat-bisim)

-- stream-equality-iso-1 : ∀ {ℓ} {A : Set ℓ} → (b : Stream A) → stream-to-Stream (Stream-to-stream b) ≡ b
-- stream-equality-iso-1 b = bisim-nat (stream-to-Stream (Stream-to-stream b)) b (helper b)

-- postulate
--   stream-equality-iso-2₁ : ∀ {ℓ} {A : Set ℓ} → (a : stream A) → (λ n → Stream-to-stream-func-x n (record { head = hd a ; tail = stream-to-Stream (tl a) })) ≡ a .fst
-- -- stream-equality-iso-2₁  a i 0 = lift tt
-- -- stream-equality-iso-2₁  a i (suc n) = {!!} , λ x → {!!}

--   stream-equality-iso-2₂ : ∀ {ℓ} {A : Set ℓ} → (a : stream A) → PathP (λ i → (n : ℕ) → π (sequence (stream-S A)) (stream-equality-iso-2₁ a i (suc n)) ≡ stream-equality-iso-2₁ a i n) (λ n i → Stream-to-stream-func-π n (record { head = hd a ; tail = stream-to-Stream (tl a) }) i) (snd a)

--   stream-to-Stream-unfold : ∀ {ℓ} {A : Set ℓ} (a : stream A) → (stream-to-Stream a) ≡ (record { head = hd a ; tail = stream-to-Stream (tl a) })

-- stream-equality-iso-2 : ∀ {ℓ} {A : Set ℓ} → (a : stream A) → Stream-to-stream (stream-to-Stream a) ≡ a
-- stream-equality-iso-2 a =
--   Stream-to-stream (stream-to-Stream a)
--     ≡⟨ refl ⟩
--   (λ n → Stream-to-stream-func-x n (stream-to-Stream a)) ,
--   (λ n → Stream-to-stream-func-π n (stream-to-Stream a))
--     ≡⟨ (λ i → ((λ n → cong (Stream-to-stream-func-x n) (stream-to-Stream-unfold a) i)) ,
--                ((λ n → cong (Stream-to-stream-func-π n) (stream-to-Stream-unfold a) i))) ⟩
--   (λ n → Stream-to-stream-func-x n (record { head = hd a ; tail = stream-to-Stream (tl a) })) ,
--   (λ n → Stream-to-stream-func-π n (record { head = hd a ; tail = stream-to-Stream (tl a) }))
--     ≡⟨ ΣPathP (stream-equality-iso-2₁ a , stream-equality-iso-2₂ a) ⟩
--   (a .fst , a .snd)
--     ≡⟨ refl ⟩
--   a ∎

-- stream-equality : ∀ {ℓ} {A : Set ℓ} -> stream A ≡ Stream A
-- stream-equality = isoToPath (iso stream-to-Stream Stream-to-stream stream-equality-iso-1 stream-equality-iso-2)

-- ------------------------------------------------------
-- -- Defining stream examples by transporting records --
-- ------------------------------------------------------

-- Zeros : Stream ℕ
-- head Zeros = 0
-- tail Zeros = Zeros

-- zeros-transported : stream ℕ
-- zeros-transported = transport (sym stream-equality) Zeros

-- -- It is now easy to show computation properties for the M-types:
-- hd-zeros-transported : hd zeros-transported ≡ 0
-- hd-zeros-transported = hd-to-head (transportRefl Zeros i0)

-- tl-zeros-transported : tl zeros-transported ≡ zeros-transported
-- tl-zeros-transported = tl-to-tail (transportRefl Zeros i0)
