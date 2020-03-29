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
open import stream

module stream-limits where

-------------------------
-- Stream using Limits --
-------------------------

lifting-cons-x : ∀ {ℓ} {A : Set ℓ} → (c : ℕ) → (n : ℕ) → (f : ℕ → A) → X (sequence (stream-S A)) n
lifting-cons-x _ 0 _ = lift tt
lifting-cons-x c (suc n) f = f c , λ _ → lifting-cons-x (suc c) n f

lifting-cons-π :
  ∀ {ℓ} {A : Set ℓ} (c : ℕ) (n : ℕ) (f : ℕ → A)
  ---------------------
  → π (sequence (stream-S A)) (lifting-cons-x c (suc n) f)
  ≡ (lifting-cons-x c n f)
lifting-cons-π _ 0 _ = refl
lifting-cons-π c (suc n) f i = f c , λ _ → lifting-cons-π (suc c) n f i

cons-2 : ∀ {ℓ} {A : Set ℓ} -> ((n : ℕ) → A) -> stream A
cons-2 f = lift-to-M (lifting-cons-x 0) (lifting-cons-π 0) f

postulate
  hd-cons-2 : ∀ {ℓ} {A : Set ℓ} (f : ℕ → A) → hd (cons-2 {A = A} f) ≡ f 0
  tl-cons-2 : ∀ {ℓ} {A : Set ℓ} (f : ℕ → A) → tl {A = A} (cons-2 f) ≡ cons-2 (f ∘ suc)

  hd-cons-2-inv : ∀ {ℓ} {A : Set ℓ} (f : ℕ → A) → hd (cons-2 f) ≡ f 0

cons-2-inv : ∀ {ℓ} {A : Set ℓ} -> stream A → (ℕ → A)
cons-2-inv x 0 = hd x
cons-2-inv x (suc n) = cons-2-inv (tl x) n

postulate
  cons-2-helper-x : ∀ {ℓ} {A : Set ℓ} b
    → (n : ℕ) → cons-2 {A = A} (cons-2-inv b) ≡ b → X (sequence (stream-S (cons-2 (cons-2-inv b) ≡ b))) n
-- cons-2-helper-x = {!!}

  cons-2-helper-π : ∀ {ℓ} {A : Set ℓ} b
    → (n : ℕ) (a : cons-2 {A = A} (cons-2-inv b) ≡ b) → π (sequence (stream-S (cons-2 (cons-2-inv b) ≡ b))) (cons-2-helper-x b (suc n) a)
    ≡ cons-2-helper-x b n a
-- cons-2-helper-π = {!!}

postulate
  cons-2-iso : ∀ {ℓ} {A : Set ℓ} (b : stream A) → (cons-2 (cons-2-inv b) ≡ b)
-- cons-2-iso {A = A} b =
--   transport (sym (stream-expand A (cons-2 (cons-2-inv b)) b))
--     ((hd (cons-2 (cons-2-inv b))
--       ≡⟨ hd-cons-2 (cons-2-inv b) ⟩
--     cons-2-inv b 0
--       ≡⟨ refl ⟩
--     hd b ∎) ,
--     (tl (cons-2 (cons-2-inv b))
--       ≡⟨ tl-cons-2 (cons-2-inv b) ⟩
--     cons-2 (cons-2-inv b ∘ suc)
--       ≡⟨ refl ⟩
--     cons-2 (cons-2-inv (tl b))
--       ≡⟨ cons-2-iso (tl b) ⟩
--     tl b ∎))

postulate
  cons-2-iso-2 : ∀ {ℓ} {A : Set ℓ} (b : ℕ → A) → (cons-2-inv (cons-2 b) ≡ b)
-- cons-2-iso-2 {A = A} b =
--   funExt (λ {0 →
--     cons-2-inv (cons-2 b) 0
--       ≡⟨ refl ⟩
--     hd (cons-2 b)
--       ≡⟨ hd-cons-2 b ⟩
--     b 0 ∎ ; (suc n) →
--     cons-2-inv (cons-2 b) (suc n)
--       ≡⟨ refl ⟩
--     cons-2-inv (tl (cons-2 b)) n
--       ≡⟨ cong (λ a → cons-2-inv a n) (tl-cons-2 b) ⟩
--     cons-2-inv (cons-2 (b ∘ suc)) n
--       ≡⟨ funExt⁻ (cons-2-iso-2 (b ∘ suc)) n ⟩
--     b (suc n) ∎})

cons-2-equality : ∀ {ℓ} {A : Set ℓ} -> (ℕ → A) ≡ stream A
cons-2-equality {A = A} =
  isoToPath (iso cons-2
                 cons-2-inv
                 cons-2-iso
                 cons-2-iso-2)

zip-2 : ∀ {ℓ} {A B : Set ℓ} → stream A × stream B → stream (A × B)
zip-2 (x , y) = cons-2 λ n → cons-2-inv x n , cons-2-inv y n

zeros : stream ℕ
zeros = cons-2 λ _ → 0

-- TODO:
postulate
  out-of-cons-2 : ∀ {ℓ} {A : Set ℓ} (f : ℕ → A) → out-fun (cons-2 f) ≡ (f 0 , λ { (lift tt) → cons-2 (λ n → f (suc n)) } )

zero-stream-tl : tl zeros ≡ zeros
zero-stream-tl = cong (λ x → snd x (lift tt)) (out-of-cons-2 (λ _ → 0))

zero-stream-hd : hd (zeros) ≡ 0
zero-stream-hd = cong fst (out-of-cons-2 (λ _ → 0))
