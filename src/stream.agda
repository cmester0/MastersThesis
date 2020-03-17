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

open import Cubical.Codata.Stream

open import M
open import helper
open import Container
open import Container-M-type

module stream where

--------------------------------------
-- Stream definitions using M-types --
--------------------------------------

stream-S : ∀ A -> Container
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Set₀) -> Set₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

-- --------------------------
-- -- Stream using M-types --
-- --------------------------

stream-pair-M : ∀ A B → stream A × stream B ≡ M (Container-product (stream-S A) (stream-S B))
stream-pair-M A B = M-product-equality (stream-S A) (stream-S B)

Container-product-streams : ∀ A B → Container-product (stream-S A) (stream-S B) ≡ stream-S (A × B)
Container-product-streams A B =
  Container-product (stream-S A) (stream-S B)
    ≡⟨ refl ⟩
  (A × B , λ x → Unit × Unit )
    ≡⟨ (λ i → (A × B) , λ _ → sym diagonal-unit i) ⟩
  (A × B , λ x → Unit ) 
    ≡⟨ refl ⟩
  stream-S (A × B) ∎

stream-pair : ∀ A B → stream A × stream B ≡ stream (A × B)
stream-pair A B = stream-pair-M A B □ λ i → M (Container-product-streams A B i)

zip : ∀ {A B} → stream A × stream B → stream (A × B)
zip {A} {B} = transport (stream-pair A B)

-------------------------
-- Stream using Limits --
-------------------------

lifting-cons-x : ∀ {A} → (c : ℕ) → (n : ℕ) → (f : ℕ → A) → X (sequence (stream-S A)) n
lifting-cons-x _ 0 _ = lift tt
lifting-cons-x c (suc n) f = f c , λ _ → lifting-cons-x (suc c) n f

lifting-cons-π :
  ∀ {A} (c : ℕ) (n : ℕ) (f : ℕ → A)
  ---------------------
  → π (sequence (stream-S A)) (lifting-cons-x c (suc n) f)
  ≡ (lifting-cons-x c n f)
lifting-cons-π _ 0 _ = refl
lifting-cons-π c (suc n) f i = f c , λ _ → lifting-cons-π (suc c) n f i

cons-2 : ∀ {A} -> ((n : ℕ) → A) -> stream A
cons-2 f = lift-to-M (lifting-cons-x 0) (lifting-cons-π 0) f

cons-2-inv : ∀ {A} -> stream A → (ℕ → A)
cons-2-inv x 0 = hd x
cons-2-inv x (suc n) = cons-2-inv (tl x) n

-- cons-2-equality : ∀ {A} -> (ℕ → A) ≡ stream A
-- cons-2-equality = isoToPath (iso cons-2 cons-2-inv (λ b → {!!}) (λ a → {!!}))

zip-2 : ∀ {A B} → stream A × stream B → stream (A × B)
zip-2 (x , y) = cons-2 λ n → cons-2-inv x n , cons-2-inv y n
  
zeros : stream ℕ
zeros = cons-2 λ _ → 0

hd-of-cons-2 : ∀ {A} (f : ℕ → A) → hd (cons-2 f) ≡ f 0
hd-of-cons-2 {A} f =
  hd (cons-2 f)
    ≡⟨ refl ⟩
  hd (lift-to-M (lifting-cons-x 0) (lifting-cons-π 0) f)
    ≡⟨ refl ⟩
  hd ((λ n → (lifting-cons-x 0) n f) , λ n i → (lifting-cons-π 0) n f i)
    ≡⟨ refl ⟩
  out-fun ((λ n → (lifting-cons-x 0) n f) , λ n i → (lifting-cons-π 0) n f i) .fst
    ≡⟨ refl ⟩
  ((λ n → (lifting-cons-x 0) n f) {!!} .fst
  , λ _ → ((λ n → (lifting-cons-x {A} 0) n f) , (λ n i → (lifting-cons-π {A} 0) n f i))) .fst
    ≡⟨ {!!} ⟩
  (lifting-cons-x 0) (suc {!!}) f .fst
    ≡⟨ refl ⟩
  f 0 ∎

-- transport (sym ((sym
--     (  (isoToPath (iso (λ {(x , y) → (λ n → x n .fst) , (λ n → x n .snd) , y})
--                        (λ {(x , (y , z)) → (λ n → (x n) , y n) , z})
--                        (λ b → refl)
--                        (λ a → refl)))
--     □ (Σ-ap-iso₂ (λ a → Σ-ap-iso₂ λ u → refl))
--     □ (Σ-ap-iso₂ (λ a → isoToPath (iso (λ {(a , b) → (λ n i → b n i .fst) , a , (λ n x → b n x .snd)})
--                                       (λ {(a , (b , c)) → b , λ n i → a n i , c n i})
--                                       (λ {(a , b) → refl})
--                                       (λ {(a , b) → refl}))))
--     □ (isoToPath (iso (λ x → ((x .fst) , (x .snd .fst)) , ((x .snd .snd .fst) , (x .snd .snd .snd))) (λ x → x .fst .fst , x .fst .snd , x .snd .fst , x .snd .snd) (λ b → refl) λ a → refl))
--     □ (sym (Σ-ap-iso (reduced-todo' S) (reduced-todo S)))
--     □ (Σ-ap-iso₂ (λ a → sym (lemma10 (B a , (λ x → a , λ x₁ → x₁)))))) □ (L-unique' {S = S})))

-- transport (sym ((sym α-iso') □ (L-unique' {S = S})))



-- Σ (S .fst) λ x → (S .snd x) -> X


-- zeros : stream ℕ
-- zeros = lifting lifting-const-x lifting-const-π 0

-- zero-stream = cons 0 zeros
-- zero-stream-2 = cons 0 (cons 0 zeros)

-- zero-stream-tl : zero-stream ≡ tl (zero-stream)
-- zero-stream-tl = λ i → {!!}

-- zero-stream-hd : hd (zero-stream-2) ≡ 0
-- zero-stream-hd = λ i → {!!}

-- zero-stream-hd : hd zeros ≡ 0
-- zero-stream-hd =
--   hd zeros
--     ≡⟨ refl ⟩
--   hd (lifting lifting-const-x lifting-const-π 0)
--     ≡⟨ refl ⟩
--   out-fun (lifting lifting-const-x lifting-const-π 0) .fst
--     ≡⟨ {!!} ⟩
--   {!!}
--     ≡⟨ {!!} ⟩
--   0 ∎

-- ------------------------------
-- -- Equality of stream types --
-- ------------------------------

-- open Stream

-- stream-to-Stream : ∀ {A} → stream A → Stream A
-- head (stream-to-Stream x) = (hd x)
-- tail (stream-to-Stream x) = (stream-to-Stream (tl x))

-- Stream-to-stream-func-x : ∀ {A} (n : ℕ) -> Stream A → X (sequence (stream-S A)) n
-- Stream-to-stream-func-x 0 x = lift tt
-- Stream-to-stream-func-x (suc n) x = head x , λ x₁ → Stream-to-stream-func-x n (tail x)

-- Stream-to-stream-func-π : ∀ {A} (n : ℕ) (a : Stream A) → π (sequence (stream-S A)) (Stream-to-stream-func-x (suc n) a) ≡ Stream-to-stream-func-x n a
-- Stream-to-stream-func-π 0 a = refl
-- Stream-to-stream-func-π (suc n) a = λ i → head a , λ _ → Stream-to-stream-func-π n (tail a) i

-- Stream-to-stream : ∀ {A : Set} -> Stream A -> stream A
-- Stream-to-stream s = lifting Stream-to-stream-func-x Stream-to-stream-func-π s

-- -- Stream-to-stream (stream-to-stream a)
-- -- Stream-to-stream (record { head = hd a ; tail = stream-to-stream (tl a) })
-- -- lifting Stream-to-stream-func-x Stream-to-stream-func-π (record { head = hd a ; tail = stream-to-Stream (tl a) })
-- -- (λ x p a → (λ n → x n a) , λ n i → p n a i) Stream-to-stream-func-x Stream-to-stream-func-π (record { head = hd a ; tail = stream-to-Stream (tl a) })
-- -- (λ a → (λ n → Stream-to-stream-func-x n a) , λ n i → Stream-to-stream-func-π n a i) (record { head = hd a ; tail = stream-to-Stream (tl a) })
--   -- First case:
--   -- (λ n → Stream-to-stream-func-x n (record { head = hd a ; tail = stream-to-Stream (tl a) }))
--     -- Zero case
--     -- Stream-to-stream-func-x 0 (record { head = hd a ; tail = stream-to-Stream (tl a) })
--     -- lift tt
--     -- N+1 case:
--     -- Stream-to-stream-func-x (suc n) (record { head = hd a ; tail = stream-to-Stream (tl a) })
--     -- (hd a , λ x₁ → Stream-to-stream-func-x n (stream-to-Stream (tl a)))
--   -- Second case:
--   -- λ n i → Stream-to-stream-func-π n (record { head = hd a ; tail = stream-to-Stream (tl a) }) i) 

-- stream-equality-iso-1-helper-0 : ∀ {A} (b : Stream A) -> (hd (Stream-to-stream b)) ≡ (head b)
-- stream-equality-iso-1-helper-0 {A} b = 
--   hd (Stream-to-stream b)
--     ≡⟨ refl ⟩
--   hd (lifting Stream-to-stream-func-x Stream-to-stream-func-π b)
--     ≡⟨ refl ⟩
--   hd ((λ n → Stream-to-stream-func-x n b) , λ n i → Stream-to-stream-func-π n b i)
--     ≡⟨ refl ⟩
--   out-fun ((λ n → Stream-to-stream-func-x n b) , (λ n i → Stream-to-stream-func-π n b i)) .fst
--     ≡⟨ refl ⟩
--   transport (sym (shift {S = stream-S A})) (((λ n → Stream-to-stream-func-x n b) , (λ n i → Stream-to-stream-func-π n b i))) .fst
--     ≡⟨ refl ⟩
--   transport (sym ((sym α-iso') □ (L-unique' {S = stream-S A}))) (((λ n → Stream-to-stream-func-x n b) , (λ n i → Stream-to-stream-func-π n b i))) .fst
--     ≡⟨ refl ⟩
--   transport (sym ((sym α-iso') □ (L-unique' {S = stream-S A}))) (((λ n → Stream-to-stream-func-x n b) , (λ n i → Stream-to-stream-func-π n b i))) .fst
--     ≡⟨ {!!} ⟩
--   head b ∎

-- stream-equality-iso-1 : ∀ {A} → (b : Stream A) → stream-to-Stream (Stream-to-stream b) ≡ b
-- stream-equality-iso-1 b =
--   stream-to-Stream (Stream-to-stream b)
--     ≡⟨ {!!} ⟩
--   stream-to-Stream (cons (hd (Stream-to-stream b)) (tl (Stream-to-stream b)))
--     ≡⟨ (λ i → stream-to-Stream (cons {!!} (tl (Stream-to-stream b)))) ⟩
--   stream-to-Stream (cons (head b) (tl (Stream-to-stream b)))
--     ≡⟨ {!!} ⟩
--   b ∎
  
-- -- stream-equality-iso-1 : ∀ {A} → (b : Stream A) → stream-to-Stream (Stream-to-stream b) ≡ b
-- -- head (stream-equality-iso-1 b i) =
-- --   (head (stream-to-Stream (Stream-to-stream b))
-- --     ≡⟨ refl ⟩
-- --   hd (Stream-to-stream b)
-- --     ≡⟨ {!!} ⟩
-- --   head b ∎) i
-- -- tail (stream-equality-iso-1 b i) =
-- --   (tail (stream-to-Stream (Stream-to-stream b))
-- --     ≡⟨ refl ⟩
-- --   (stream-to-Stream (tl (Stream-to-stream b)))
-- --     ≡⟨ {!!} ⟩
-- --   stream-to-Stream (Stream-to-stream (tail b))
-- --     ≡⟨ stream-equality-iso-1 (tail b) ⟩
-- --   tail b ∎) i

-- -- stream-to-Stream : ∀ {A} → stream A → Stream A
-- -- head (stream-to-Stream x) = (hd x)
-- -- tail (stream-to-Stream x) = (stream-to-Stream (tl x))

-- -- stream-equality-iso-2₁ : ∀ {A} → (a : stream A) → (λ n → Stream-to-stream-func-x n (record { head = hd a ; tail = stream-to-Stream (tl a) })) ≡ a .fst
-- -- stream-equality-iso-2₁  a i 0 = lift tt
-- -- stream-equality-iso-2₁  a i (suc n) = {!!} , λ x → {!!}

-- -- stream-equality-iso-2 : ∀ {A} → (a : stream A) → Stream-to-stream (stream-to-Stream a) ≡ a
-- -- stream-equality-iso-2 a =
-- --   Stream-to-stream (stream-to-Stream a)
-- --     ≡⟨ refl ⟩
-- --   (λ n → Stream-to-stream-func-x n (stream-to-Stream a)) ,
-- --   (λ n i → Stream-to-stream-func-π n (stream-to-Stream a) i)
-- --     ≡⟨ {!!} ⟩
-- --   (λ n → Stream-to-stream-func-x n (record { head = hd a ; tail = stream-to-Stream (tl a) })) ,
-- --   (λ n i → Stream-to-stream-func-π n (record { head = hd a ; tail = stream-to-Stream (tl a) }) i)
-- --     ≡⟨ (λ i → stream-equality-iso-2₁ a i , {!!}) ⟩
-- --   (a .fst , a .snd)
-- --     ≡⟨ refl ⟩
-- --   a ∎

-- -- stream-equality : ∀ {A} -> stream A ≡ Stream A
-- -- stream-equality = isoToPath (iso stream-to-Stream Stream-to-stream stream-equality-iso-1 stream-equality-iso-2)

-- -- -- Defining stream examples by transporting records

-- -- Zeros : Stream ℕ
-- -- head Zeros = 0
-- -- tail Zeros = Zeros

-- -- zeros : stream ℕ
-- -- zeros = transport (sym stream-equality) Zeros

