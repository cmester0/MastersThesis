{-# OPTIONS --cubical --guardedness #-}

module stream where

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Isomorphism

open import Cubical.Codata.Stream
open Stream
open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Container

open import Cubical.Codata.M.AsLimit.stream
open Cubical.Codata.M.AsLimit.stream public -- Re-export
open import Coalg.Coinduction
open import Coalg.Properties

-----------------
-- Coinduction --
-----------------

open bisimulation

record _∼stream_ {A} (x y : stream A) : Set where
  coinductive
  field
    ∼hd : (hd x) ≡ (hd y)
    ∼tl : (tl x) ∼stream (tl y)
  
open _∼stream_

stream-bisim : ∀ {A} → bisimulation (stream-S A) M-coalg _∼stream_
αᵣ (stream-bisim) (x , y , r) = hd x , (λ {tt → tl x , (tl y) , ∼tl r})
rel₁ (stream-bisim) = refl
rel₂ (stream-bisim) = funExt λ {(x , y , r) → ΣPathP (sym (∼hd r) , refl)}

stream-coinduction : ∀ {A} {m m' : stream A} → m ∼stream m' → m ≡ m'
stream-coinduction = coinduction _∼stream_ stream-bisim

------------------------------
-- Equality of stream types --
------------------------------

stream-to-Stream : ∀ {A : Type₀} → stream A → Stream A
head (stream-to-Stream x) = hd x
tail (stream-to-Stream x) = stream-to-Stream (tl x)

private
  Stream-to-stream-func-x : ∀ {A : Type₀} (n : ℕ) → Stream A → Wₙ (stream-S A) n
  Stream-to-stream-func-x 0 x = lift tt
  Stream-to-stream-func-x (suc n) x = head x , λ _ → Stream-to-stream-func-x n (tail x)

  Stream-to-stream-func-π : ∀ {A : Type₀} (n : ℕ) (x : Stream A) → πₙ (stream-S A) (Stream-to-stream-func-x (suc n) x) ≡ Stream-to-stream-func-x n x
  Stream-to-stream-func-π 0 x = refl {x = lift tt}
  Stream-to-stream-func-π (suc n) x = λ i → head x , λ _ → Stream-to-stream-func-π n (tail x) i

Stream-to-stream : ∀ {A : Type₀} → Stream A → stream A
Stream-to-stream s = lift-to-M Stream-to-stream-func-x Stream-to-stream-func-π s

hd-to-head : ∀ {A : Type₀} (b : Stream A) → hd (Stream-to-stream b) ≡ head b
hd-to-head {A = A} b = refl

head-to-hd : ∀ {A : Type₀} (b : stream A) → head (stream-to-Stream b) ≡ hd b
head-to-hd {A = A} b = refl

tail-to-tl : ∀ {A : Type₀} (b : stream A) → tail (stream-to-Stream b) ≡ stream-to-Stream (tl b)
tail-to-tl b = refl

private
  tail-eq-x : ∀ {A : Type₀} → (b : Stream A) (n : ℕ) → fst (tl (Stream-to-stream b)) n ≡ fst (Stream-to-stream (tail b)) n
  tail-eq-x {A = A} b n = sym (transport-filler (λ i → Wₙ (stream-S A) n) (Stream-to-stream-func-x n (tail b)))

  postulate
    tail-eq-π :
      ∀ {A : Type₀} → (b : Stream A) → (n : ℕ) →
      PathP (λ i → πₙ (stream-S A) (tail-eq-x b (suc n) i) ≡ tail-eq-x b n i)
        (snd (tl (Stream-to-stream b)) n)
        (Stream-to-stream-func-π n (tail b))

tl-to-tail :
  ∀ {A : Type₀} (b : Stream A)
  → tl (Stream-to-stream b) ≡ Stream-to-stream (tail b)
tl-to-tail {A = A} b =
  stream-coinduction (helper b)
  where
    helper : ∀ (b : stream A) → tl (Stream-to-stream b) ∼stream Stream-to-stream (tail b)
    helper = {!!}

  -- ΣPathP (funExt (tail-eq-x b) , λ i n j → tail-eq-π b n i j)

{-# NON_TERMINATING #-}
stream-equality-iso-1 : ∀ {A : Type₀} → (b : Stream A) → stream-to-Stream (Stream-to-stream b) ≡ b
stream-equality-iso-1 b = bisim (helper b)
  where
    open Equality≅Bisimulation
    open _≈_
    helper : forall b -> stream-to-Stream (Stream-to-stream b) ≈ b
    ≈head (helper b) = refl
    ≈tail (helper b) =
      subst (λ x → x ≈ tail b)
        (stream-to-Stream (Stream-to-stream (tail b))
          ≡⟨ cong stream-to-Stream (sym (tl-to-tail b)) ⟩
        stream-to-Stream (tl (Stream-to-stream b))
          ≡⟨ sym (tail-to-tl (Stream-to-stream b)) ⟩
        tail (stream-to-Stream (Stream-to-stream b)) ∎)
        (helper (tail b))

  -- bisim-nat (stream-to-Stream (Stream-to-stream b)) b (helper b)
  -- where  
  --   nth : ∀ {A : Type₀} → ℕ → (b : Stream A) → A
  --   nth 0 b = head b
  --   nth (suc n) b = nth n (tail b)

  --   helper : ∀ {A : Type₀} → (b : Stream A) → ((n : ℕ) → nth n (stream-to-Stream (Stream-to-stream b)) ≡ nth n b)
  --   helper b 0 = head-to-hd (Stream-to-stream b) ∙ hd-to-head b
  --   helper b (suc n) =
  --     nth (suc n) (stream-to-Stream (Stream-to-stream b))
  --       ≡⟨ refl ⟩
  --     nth n (tail (stream-to-Stream (Stream-to-stream b)))
  --       ≡⟨ cong (nth n) (tail-to-tl (Stream-to-stream b) ∙ cong stream-to-Stream (tl-to-tail b)) ⟩
  --     nth n (stream-to-Stream (Stream-to-stream (tail b)))
  --       ≡⟨ helper (tail b) n ⟩
  --     nth n (tail b) ∎

  --   bisim-nat : ∀ {A : Type₀} → (a b : Stream A) → ((n : ℕ) → nth n a ≡ nth n b) → a ≡ b
  --   bisim-nat a b nat-bisim = bisim (bisim-nat' a b nat-bisim)
  --     where
  --       open Equality≅Bisimulation
  --       open _≈_

  --       bisim-nat' : ∀ {A : Type₀} → (a b : Stream A) → ((n : ℕ) → nth n a ≡ nth n b) → a ≈ b
  --       ≈head (bisim-nat' a b nat-bisim) = nat-bisim 0
  --       ≈tail (bisim-nat' a b nat-bisim) = bisim-nat' (tail a) (tail b) (nat-bisim ∘ suc)

-- private
--   stream-equality-iso-2-x : ∀ {A : Type₀} → (a : stream A) (n : ℕ) → Stream-to-stream-func-x n (stream-to-Stream a) ≡ fst a n
--   stream-equality-iso-2-x a 0 = refl
--   stream-equality-iso-2-x {A} a (suc n) =
--     Stream-to-stream-func-x (suc n) (stream-to-Stream a)
--       ≡⟨ refl ⟩
--     (head (stream-to-Stream a) , (λ _ → Stream-to-stream-func-x n (tail (stream-to-Stream a))))
--       ≡⟨ ΣPathP (head-to-hd a , funExt λ _ → cong (Stream-to-stream-func-x n) (tail-to-tl a)) ⟩
--     (hd a , (λ _ → Stream-to-stream-func-x n (stream-to-Stream (tl a))))
--       ≡⟨ ΣPathP (refl , funExt λ _ → stream-equality-iso-2-x (tl a) n) ⟩
--     (hd a , (λ _ → fst (tl a) n))
--       ≡⟨ ΣPathP (refl , refl) ⟩
--     (out-fun a .fst , (λ _ → fst (tl a) n))
--       ≡⟨ ΣPathP (refl , refl) ⟩
--     (fst (fst a (suc 0)) , (λ _ → fst (tl a) n))
--       ≡⟨ ΣPathP (temp n , refl) ⟩
--     (fst (fst a (suc n)) , (λ _ → fst (tl a) n))
--       ≡⟨ ΣPathP (refl , funExt λ _ → temp') ⟩
--     fst (fst a (suc n)) , snd (fst a (suc n))
--       ≡⟨ refl ⟩
--     fst a (suc n) ∎
--     where
--       temp : ∀ (n : ℕ) → fst (fst a (suc 0)) ≡ fst (fst a (suc n))
--       temp 0 = refl
--       temp (suc n) = temp n ∙ cong fst (sym (snd a (suc n)))

--       temp' : fst (tl a) n ≡ snd (fst a (suc n)) tt
--       temp' = sym (transport-filler (λ i → Wₙ (stream-S A) n) (a .fst (suc n) .snd tt))

--   postulate
--     stream-equality-iso-2-π :
--       ∀ {A : Type₀} → (a : stream A) (n : ℕ)
--       → PathP (λ i → πₙ (stream-S A) (funExt (stream-equality-iso-2-x a) i (suc n)) ≡ funExt (stream-equality-iso-2-x a) i n)
--         (Stream-to-stream-func-π n (stream-to-Stream a))
--         (snd a n)

{-# NON_TERMINATING #-}
stream-equality-iso-2 : ∀ {A : Type₀} → (a : stream A) → Stream-to-stream (stream-to-Stream a) ≡ a
stream-equality-iso-2 {A} a =
  stream-coinduction (helper a)
  where
    helper : (a : stream A) → Stream-to-stream (stream-to-Stream a) ∼stream a
    ∼hd (helper a) = refl
    ∼tl (helper a) = subst (λ x → x ∼stream tl a)
      (Stream-to-stream (stream-to-Stream (tl a))
        ≡⟨ cong Stream-to-stream (sym (tail-to-tl a)) ⟩
      Stream-to-stream (tail (stream-to-Stream a))
        ≡⟨ sym (tl-to-tail (stream-to-Stream a)) ⟩
      tl (Stream-to-stream (stream-to-Stream a)) ∎) (helper (tl a))

  -- Stream-to-stream (stream-to-Stream a)
  --   ≡⟨ refl ⟩
  -- lift-to-M Stream-to-stream-func-x Stream-to-stream-func-π (stream-to-Stream a)
  --   ≡⟨ refl ⟩
  -- (λ n → Stream-to-stream-func-x n (stream-to-Stream a)) ,
  -- (λ n → Stream-to-stream-func-π n (stream-to-Stream a))
  --   ≡⟨ ΣPathP (funExt (stream-equality-iso-2-x a) , λ i n j → stream-equality-iso-2-π a n i j) ⟩
  -- a ∎

stream-equality : ∀ {A : Type₀} → stream A ≡ Stream A
stream-equality = isoToPath (iso stream-to-Stream Stream-to-stream stream-equality-iso-1 stream-equality-iso-2)

------------------------------------------------------
-- Defining stream examples by transporting records --
------------------------------------------------------

-- Zeros defined as a record type
Zeros : Stream ℕ
head Zeros = 0
tail Zeros = Zeros

zeros-transported : stream ℕ
zeros-transported = transport (sym stream-equality) Zeros

-- It is now easy to show computation properties for the M-types:
hd-zeros-transported : hd zeros-transported ≡ 0
hd-zeros-transported = hd-to-head (transportRefl Zeros i0)

tl-zeros-transported : tl zeros-transported ≡ zeros-transported
tl-zeros-transported = tl-to-tail (transportRefl Zeros i0)

-- zeros defined for stream M-type
zeros : stream ℕ
zeros = lift-direct-M zeros-x zeros-π
  where
    zeros-x : (n : ℕ) → Wₙ (stream-S ℕ) n
    zeros-x 0 = lift tt
    zeros-x (suc n) = 0 , (λ _ → zeros-x n)

    zeros-π : (n : ℕ) → πₙ (stream-S ℕ) (zeros-x (suc n)) ≡ zeros-x n
    zeros-π 0 i = lift tt
    zeros-π (suc n) i = 0 , (λ _ → zeros-π n i)
