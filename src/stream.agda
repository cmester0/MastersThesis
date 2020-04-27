{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Transport

open import Cubical.Codata.Stream

-- open import Cubical.Codata.Stream

open import M
open import helper
open import Container
open import Container-M-type
open import Coalg

open import Cubical.Functions.Embedding

open import Cubical.Foundations.Path

module stream where

--------------------------------------
-- Stream definitions using M-types --
--------------------------------------

stream-S : ∀ (A : Set) -> Container
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Set) -> Set
stream A = M (stream-S A)

cons : ∀ {A : Set} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A : Set} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A : Set} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

-------------------------------
-- Expanding stream equality --
-------------------------------

stream-expand-2 : ∀ {A : Set} {s t : stream A} → (s ≡ t) ≡ (cons (hd s) (tl s) ≡ cons (hd t) (tl t))
stream-expand-2 = sym in-out-id

stream-expand-1 : ∀ {A : Set} {a c : A} {b d : stream A} → (cons a b ≡ cons c d) ≡ (a ≡ c) × (b ≡ d)
stream-expand-1 {a = a} {c} {b} {d} =
  (cons a b ≡ cons c d)
    ≡⟨ in-inj-x ⟩
  ((a , (λ { tt → b })) ≡ (c , (λ { tt → d })))
    ≡⟨ sym Σ-split ⟩
  (Σ (a ≡ c) (λ _ → (λ { tt → b }) ≡ λ { tt → d }))
     ≡⟨ isoToPath (iso (λ {(x , y) → x , funExt⁻ y tt}) (λ {(x , y) → x , funExt (λ { tt → y})}) (λ b₁ → refl) λ a₁ → refl) ⟩
  (Σ (a ≡ c) (λ _ → b ≡ d))
     ≡⟨ sym A×B≡A×ΣB ⟩
  ((a ≡ c) × (b ≡ d)) ∎

stream-expand : ∀ (A : Set) (s t : stream A) → (s ≡ t) ≡ (hd s ≡ hd t) × (tl s ≡ tl t)
stream-expand A s t = stream-expand-2 ∙ stream-expand-1

hd-is-hd : ∀ (A : Set) (x : A) (xs : stream A) → hd (cons x xs) ≡ x
hd-is-hd A x xs =
  hd (cons x xs)
    ≡⟨ cong (λ a → a .fst) (funExt⁻ (out-inverse-in {S = stream-S A}) (x , λ { tt → xs })) ⟩
  x ∎

tl-is-tl : ∀ (A : Set) (x : A) (xs : stream A) → tl (cons x xs) ≡ xs
tl-is-tl A x xs =
  tl (cons x xs)
    ≡⟨ cong (λ a → a .snd tt) (funExt⁻ (out-inverse-in {S = stream-S A}) (x , λ { tt → xs })) ⟩
  xs ∎

--------------------------
-- Stream using M-types --
--------------------------

stream-pair-M : ∀ (A B : Set) → stream A × stream B ≡ M (Container-product (stream-S A) (stream-S B))
stream-pair-M A B = M-product-equality (stream-S A) (stream-S B)

Container-product-streams : ∀ (A B : Set) → Container-product (stream-S A) (stream-S B) ≡ stream-S (A × B)
Container-product-streams A B =
  Container-product (stream-S A) (stream-S B)
    ≡⟨ refl ⟩
  (A × B , λ x → Unit × Unit )
    ≡⟨ (λ i → (A × B) , λ _ → sym diagonal-unit i) ⟩
  (A × B , λ x → Unit )
    ≡⟨ refl ⟩
  stream-S (A × B) ∎

stream-pair : ∀ (A B : Set) → stream A × stream B ≡ stream (A × B)
stream-pair A B = stream-pair-M A B ∙ λ i → M (Container-product-streams A B i)

zip : ∀ {A B : Set} → stream A × stream B → stream (A × B)
zip {A = A} {B} = transport (stream-pair A B)

------------------------------
-- Equality of stream types --
------------------------------

open Stream
open Equality≅Bisimulation
open _≈_

stream-to-Stream : ∀ {A : Set} → stream A → Stream A
head (stream-to-Stream x) = (hd x)
tail (stream-to-Stream x) = (stream-to-Stream (tl x))

Stream-to-stream-func-x : ∀ {A : Set} (n : ℕ) -> Stream A → X (sequence (stream-S A)) n
Stream-to-stream-func-x 0 x = lift tt
Stream-to-stream-func-x (suc n) x = head x , λ _ → Stream-to-stream-func-x n (tail x)

Stream-to-stream-func-π : ∀ {A : Set} (n : ℕ) (a : Stream A) → π (sequence (stream-S A)) (Stream-to-stream-func-x (suc n) a) ≡ Stream-to-stream-func-x n a
Stream-to-stream-func-π 0 a = refl {x = lift tt}
Stream-to-stream-func-π (suc n) a = λ i → head a , λ _ → Stream-to-stream-func-π n (tail a) i

Stream-to-stream : ∀ {A : Set} -> Stream A -> stream A
Stream-to-stream s = lift-to-M Stream-to-stream-func-x Stream-to-stream-func-π s

postulate
  hd-to-head : ∀ {A : Set} (b : Stream A) → hd (Stream-to-stream b) ≡ head b
-- hd-to-head {A = A} b = refl -- (can compute)

head-to-hd : ∀ {A : Set} (b : stream A) → head (stream-to-Stream b) ≡ hd b
head-to-hd {A = A} b = refl

tail-to-tl : ∀ {A : Set} (b : stream A) → tail (stream-to-Stream b) ≡ stream-to-Stream (tl b)
tail-to-tl b = refl

-- tl-to-tail : ∀ {A : Set} (b : Stream A) → tl (Stream-to-stream b) ≡ Stream-to-stream (tail b)
-- tl-to-tail {A = A} b =
--   tl (Stream-to-stream b)
--     ≡⟨ refl ⟩
--   (λ n → transport (refl {x = W (stream-S A) n}) (Stream-to-stream-func-x n (tail b))) ,
--   (λ n i → (transport (isoToPath (compIso (pathToIso (cong (λ a → a) (PathP≡Path (λ x → Lift Unit → W (stream-S A) n) (πₙ (stream-S A) ∘ (λ (_ : Lift Unit) → Stream-to-stream-func-x (suc n) (tail b))) (λ (_ : Lift Unit) → Stream-to-stream-func-x n (tail b)))))
--             (compIso (sym-iso (≡-rel-a-inj-x-Iso (pathToIso (refl {x = Lift Unit → W (stream-S A) n}))))
--             (compIso (pathToIso
--               (cong (λ a → (λ (_ : Lift Unit) → a) ≡ (λ (_ : Lift Unit) → transport (refl {x = W (stream-S A) n}) (Stream-to-stream-func-x n (tail b))))
--                     (sym (substComposite (λ k → W (stream-S A) n) (refl {x = head b})
--                          (α-iso-step-5-Iso-helper0 {S = stream-S A} (λ n → head b) (λ n → refl {x = head b}) n)
--                          (πₙ (stream-S A) (Stream-to-stream-func-x (suc n) (tail b)))))))
--                      (pathToIso (cong (λ a → a ≡ (λ (_ : Lift Unit) → transport (refl {x = W (stream-S A) n}) (Stream-to-stream-func-x n (tail b)))) (funExt λ (_ : Lift Unit) →
--                                 (substCommSlice (λ k → W (stream-S A) (suc n))
--                                                 (λ k → W (stream-S A) n)
--                                                 (λ a x  → (πₙ (stream-S A)) x)
--                                                 (α-iso-step-5-Iso-helper0 {S = stream-S A} (λ n → head b) (λ n i → head b) n)
--                                                 (Stream-to-stream-func-x (suc n) (tail b))))))))))
--                     (funExt λ _ → Stream-to-stream-func-π n (tail b))) i (lift tt))
--     ≡⟨ refl ⟩
--   (λ n → transport (refl {x = W (stream-S A) n}) (Stream-to-stream-func-x n (tail b))) ,
--   (λ n i → (transport (isoToPath (compIso (pathToIso (cong (λ a → a) (PathP≡Path (λ x → Lift Unit → W (stream-S A) n) (πₙ (stream-S A) ∘ (λ (_ : Lift Unit) → Stream-to-stream-func-x (suc n) (tail b))) (λ (_ : Lift Unit) → Stream-to-stream-func-x n (tail b)))))
--             (compIso (sym-iso (
--   let x = λ (_ : Lift Unit) → transport (refl {x = W (stream-S A) n}) (πₙ (stream-S A) (Stream-to-stream-func-x (suc n) (tail b)))
--       y = λ (_ : Lift Unit) → Stream-to-stream-func-x n (tail b)
--   in
--   transport (refl {x = Lift Unit → W (stream-S A) n}) x ≡ transport (refl {x = Lift Unit → W (stream-S A) n}) y
--     Iso⟨ iso (λ x₁ t → x₁)
--              (λ x₁ → x₁ (lift tt))
--              refl-fun
--              refl-fun ⟩
--   (∀ (t : Lift Unit) -> (transport (refl {x = Lift Unit → W (stream-S A) n}) x ≡ transport (refl {x = Lift Unit → W (stream-S A) n}) y))
--     Iso⟨ cong-iso (λ a → ∀ (x : Lift Unit) → a x) (funExt (\(_ : Lift Unit) ->
--            sym (ua (cong (transport (refl {x = Lift Unit → W (stream-S A) n})) ,
--                     (isEquiv→isEmbedding (equivIsEquiv (isoToEquiv (pathToIso (refl {x = (_ : Lift Unit) → W (stream-S A) n})))))
--                       (λ (_ : Lift Unit) → transport (refl {x = W (stream-S A) n}) (πₙ (stream-S A) (Stream-to-stream-func-x (suc n) (tail b))))
--                       (λ (_ : Lift Unit) → Stream-to-stream-func-x n (tail b)))))) ⟩
--   (∀ (t : Lift Unit) -> x ≡ y)
--      Iso⟨ iso (λ x₁ → x₁ (lift tt))
--               (λ x₁ t → x₁)
--               refl-fun
--               refl-fun ⟩
--   x ≡ y ∎Iso)) 
--             (compIso (pathToIso
--               (cong (λ a → (λ (_ : Lift Unit) → a) ≡ (λ (_ : Lift Unit) → transport (refl {x = W (stream-S A) n}) (Stream-to-stream-func-x n (tail b))))
--                     (sym (substComposite (λ k → W (stream-S A) n) (refl {x = head b})
--                          (α-iso-step-5-Iso-helper0 {S = stream-S A} (λ n → head b) (λ n → refl {x = head b}) n)
--                          (πₙ (stream-S A) (Stream-to-stream-func-x (suc n) (tail b)))))))
--                      (pathToIso (cong (λ a → a ≡ (λ (_ : Lift Unit) → transport (refl {x = W (stream-S A) n}) (Stream-to-stream-func-x n (tail b)))) (funExt λ (_ : Lift Unit) →
--                                 (substCommSlice (λ k → W (stream-S A) (suc n))
--                                                 (λ k → W (stream-S A) n)
--                                                 (λ a x  → (πₙ (stream-S A)) x)
--                                                 (α-iso-step-5-Iso-helper0 {S = stream-S A} (λ n → head b) (λ n i → head b) n)
--                                                 (Stream-to-stream-func-x (suc n) (tail b))))))))))
--                     (funExt λ _ → Stream-to-stream-func-π n (tail b))) i (lift tt))
--       ≡⟨ {!!} ⟩ 
--   (λ n → Stream-to-stream-func-x n (tail b)) ,
--   (λ n → Stream-to-stream-func-π n (tail b))
--     ≡⟨ refl ⟩
--   Stream-to-stream (tail b) ∎
--   where
--     open Iso

-- postulate
--   tl-to-tail : ∀ {A : Set} (b : Stream A) → tl (Stream-to-stream b) ≡ Stream-to-stream (tail b) -- should this be able to compute ??

tl-to-tail : ∀ {A : Set} (b : Stream A) → tl (Stream-to-stream b) ≡ Stream-to-stream (tail b)
tl-to-tail = {!!}

nth : ∀ {A : Set} → ℕ → (b : Stream A) → A
nth 0 b = head b
nth (suc n) b = nth n (tail b)

helper : ∀ {A : Set} → (b : Stream A) → ((n : ℕ) → nth n (stream-to-Stream (Stream-to-stream b)) ≡ nth n b)
helper b 0 = head-to-hd (Stream-to-stream b) ∙ hd-to-head b
helper b (suc n) =
  nth (suc n) (stream-to-Stream (Stream-to-stream b))
    ≡⟨ refl ⟩
  nth n (tail (stream-to-Stream (Stream-to-stream b)))
    ≡⟨ cong (nth n) (tail-to-tl (Stream-to-stream b) ∙ cong stream-to-Stream (tl-to-tail b)) ⟩
  nth n (stream-to-Stream (Stream-to-stream (tail b)))
    ≡⟨ helper (tail b) n ⟩
  nth n (tail b) ∎

bisim-nat' : ∀ {A : Set} → (a b : Stream A) → ((n : ℕ) → nth n a ≡ nth n b) -> a ≈ b
≈head (bisim-nat' a b nat-bisim) = nat-bisim 0
≈tail (bisim-nat' a b nat-bisim) = bisim-nat' (tail a) (tail b) (nat-bisim ∘ suc)

bisim-nat : ∀ {A : Set} → (a b : Stream A) → ((n : ℕ) → nth n a ≡ nth n b) -> a ≡ b
bisim-nat a b nat-bisim = bisim (bisim-nat' a b nat-bisim)

stream-equality-iso-1 : ∀ {A : Set} → (b : Stream A) → stream-to-Stream (Stream-to-stream b) ≡ b
stream-equality-iso-1 b = bisim-nat (stream-to-Stream (Stream-to-stream b)) b (helper b)

postulate
  stream-equality-iso-2₁ : ∀ {A : Set} → (a : stream A) (n : ℕ) → Stream-to-stream (stream-to-Stream a) .fst n ≡ a .fst n
-- stream-equality-iso-2₁ (a , b) 0 =
--   Stream-to-stream (stream-to-Stream (a , b)) .fst 0
--     ≡⟨ refl ⟩
--   Stream-to-stream-func-x 0 (stream-to-Stream (a , b))
--     ≡⟨ refl ⟩
--   lift tt
--     ≡⟨ refl ⟩
--   a 0 ∎
-- stream-equality-iso-2₁ {A = A} (a , b) (suc n) =
--   Stream-to-stream (stream-to-Stream (a , b)) .fst (suc n)
--     ≡⟨ refl ⟩
--   Stream-to-stream-func-x (suc n) (stream-to-Stream (a , b))
--     ≡⟨ refl ⟩
--   (hd (a , b) , λ _ → Stream-to-stream-func-x {A = A} n (stream-to-Stream {A = A} (tl (a , b))))
--     ≡⟨ {!!} ⟩ -- cong (λ k → hd (a , b) , λ _ → k) (stream-equality-iso-2₁-x (a , b) (suc n))
--   (hd (a , b) , λ _ → tl (a , b) .fst n)
--     ≡⟨ {!!} ⟩
--   a (suc n) ∎

postulate
  stream-equality-iso-2 : ∀ {A : Set} → (a : stream A) → Stream-to-stream (stream-to-Stream a) ≡ a
-- stream-equality-iso-2 (a , b) =
--   Stream-to-stream (stream-to-Stream (a , b))
--     ≡⟨ refl ⟩
--   (λ n → Stream-to-stream-func-x n (stream-to-Stream (a , b))) ,
--   (λ n → Stream-to-stream-func-π n (stream-to-Stream (a , b)))
--     ≡⟨ (λ i → (λ n → stream-equality-iso-2₁ (a , b) n i) , {!!}) ⟩
--   (a , b) ∎

stream-equality : ∀ {A : Set} -> stream A ≡ Stream A
stream-equality = isoToPath (iso stream-to-Stream Stream-to-stream stream-equality-iso-1 stream-equality-iso-2)

------------------------------------------------------
-- Defining stream examples by transporting records --
------------------------------------------------------

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
