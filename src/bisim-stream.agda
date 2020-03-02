{-# OPTIONS --cubical --guardedness #-} --safe
module bisim-stream where

open import itree
open import M

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

-- open import Cubical.HITs.SetQuotients

open import Cubical.Codata.Stream
-- open import Agda.Builtin.Coinduction
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Agda.Builtin.Coinduction
open import Cubical.Data.Prod
open import Coalg

open import stream

-- Bisimulation principle for streams
record stream≈ {A} (x y : stream A) : Set where
  coinductive
  field
    hd≈ : hd x ≡ hd y
    tl≈ : stream≈ (tl x) (tl y)

open stream≈

{-# NON_TERMINATING #-}
bisimR : ∀ (A : Set₀) -> (stream A) -> (stream A) -> Set
bisimR A xs ys = (hd xs ≡ hd ys) × bisimR A (tl xs) (tl ys)

a : ∀ {A} -> ∀ (m m' : stream A) -> stream≈ m m' -> m ≡ m'
a {A} = coinduction (A , (λ _ → Unit)) stream≈ (record { αᵣ = λ x → {!!} , (λ x₁ → x)
                                                        ; rel₁ = λ i a₁ → hd≈ (a₁ .snd .snd) i , λ { tt → a _ _ (tl≈ (a₁ .snd .snd)) {!!} }
                                                        ; rel₂ = {!!} }) -- (out-fun {S = stream-S A} (a₁ .fst))a

stream-bisim : ∀ {A} {x y : stream A} (p : stream≈ {A} x y) ->  x ≡ y
stream-bisim {A = A} {x = x} {y = y} s i = transp (λ i₁ → {!!}) i (cons {A = A} (hd≈ s i) (stream-bisim (tl≈ s) i)) -- (hd≈ s i) ? -- (stream-bisim (tl≈ s) i)

-- Comparing two stream of ones

-- ones : stream ℕ
-- ones = cons 1 ones

----------------------------------
-- Help the termination checker --
----------------------------------

-- postulate
--   stream-equiv : Stream ≡ stream 

-------------------------------
-- Properties of definitions --
-------------------------------

-- eta-helper : ∀ {A} (x : stream A) -> ( out-fun x .fst , λ { tt -> out-fun x .snd tt } ) ≡ out-fun x
-- eta-helper = λ x i → out-fun x .fst , λ tt → out-fun x .snd tt

-- eta-helper-2 : ∀ {A} (x : stream A) -> in-fun ( out-fun x .fst , λ { tt -> out-fun x .snd tt } ) ≡ cons {A = A} (hd x) (tl x)
-- eta-helper-2 = λ x -> refl

-- eta-helper-3 : ∀ {A} (x : stream A) -> in-fun (out-fun x) ≡ cons {A = A} (hd x) (tl x)
-- eta-helper-3 = λ x -> refl

-- eta : ∀ {A} x -> x ≡ cons {A = A} (hd x) (tl x)
-- eta {A} = λ x -> λ i ->
--   compPath-filler
--     {x = x}
--     {y = in-fun (out-fun x)}
--     {z = cons {A = A} (hd x) (tl x)}
--       (sym (in-inverse-out-x x))
--       (eta-helper-3 x)
--       i i

-- bisim-helper : ∀ {A} {x y : stream A} -> cons {A = A} (hd x) (tl x) ≡ cons {A = A} (hd y) (tl y) -> x ≡ y
-- bisim-helper {A} {xa} {ya} = λ p i →
--   compPath-filler
--     (λ j ->
--       compPath-filler
--         (eta xa)
--         p
--         j j)
--     (sym (eta ya))
--     i i

-- bisim-helper-2 : ∀ {A} {x y : stream A} -> hd x ≡ hd y -> tl x ≡ tl y -> cons {A = A} (hd x) (tl x) ≡ cons {A = A} (hd y) (tl y)
-- bisim-helper-2 {A} = λ p q i → cons (p i) (q i)
  
-- ----------------------------
-- -- Bisimulation Principle --
-- ----------------------------

-- record stream≈ {A} (x y : stream A) : Set where
--   coinductive
--   field
--     hd≈ : hd x ≡ hd y
--     tl≈ : stream≈ (tl x) (tl y)

-- open stream≈

-- {-# NON_TERMINATING #-}
-- stream-bisim' : ∀ {A} {x y : stream A} (p : stream≈ {A} x y) ->  x ≡ y
-- stream-bisim' {A} {x} {y} s = bisim-helper (bisim-helper-2 (hd≈ s) (stream-bisim' (tl≈ s)))

-- stream-bisim : ∀ {A} {x y : stream A} (p : stream≈ {A} x y) ->  x ≡ y
-- stream-bisim {A} {x} {y} s = bisim-helper (bisim-helper-2 (hd≈ s) (stream-bisim' (tl≈ s)))

-- stream-misib : ∀ {A} {x y} -> x ≡ y -> stream≈ {A} x y
-- hd≈ (stream-misib p) = λ i -> hd (p i)
-- tl≈ (stream-misib p) = stream-misib (λ i -> tl (p i))

-- iso1 : {A : Type₀} → {x y : stream A} → (p : x ≡ y) → stream-bisim {A = A} (stream-misib {A = A} p) ≡ p
-- iso1 p i j = {!!} , {!!}
-- -- (bisim-helper-2 (λ i₁ → hd (p i)) λ i₁ → tl (p i))

-- iso2 : {A : Type₀} → {x y : stream A} → (p : stream≈ x y) → stream-misib (stream-bisim p) ≡ p
-- hd≈ (iso2 p i) j = {!!} -- hd≈ p
-- tl≈ (iso2 p i) = {!!} -- iso2 (tl≈ p) i

-- path≃stream≈ : {A : Type₀} → {x y : stream A} → (x ≡ y) ≃ (stream≈ x y)
-- path≃stream≈ = isoToEquiv (iso {!!} stream-bisim iso2 iso1)

-- open Stream

-- stream-to-Stream : ∀ {A} -> stream A -> Stream A
-- head (stream-to-Stream x) = hd x
-- tail (stream-to-Stream x) = stream-to-Stream (tl x)

-- {-# NON_TERMINATING #-}
-- Stream-to-stream' : ∀ {A} -> Stream A -> stream A
-- Stream-to-stream' x = cons (head x) (Stream-to-stream' (tail x))

-- Stream-to-stream : ∀ {A} -> Stream A -> stream A
-- Stream-to-stream x = cons (head x) (Stream-to-stream' (tail x))

-- helper : ∀ {A} x -> stream-to-Stream {A} (Stream-to-stream x) ≡ x
-- helper x = λ i → {!!}

-- helper2 : ∀ {A} x -> Stream-to-stream {A} (stream-to-Stream x) ≡ x
-- helper2 x = λ i → {!!}

-- -- stream-equiv : stream ≡ Stream
-- -- stream-equiv i A = ua {A = stream A} {B = Stream A} ( stream-to-Stream , record { equiv-proof = λ y → (Stream-to-stream y , helper y) , λ y₁ i₁ → {!!} , {!!} }) i

-- stream-equiv2 : Stream ≡ stream
-- stream-equiv2 i A = ua {A = Stream A} {B = stream A} ( Stream-to-stream , record { equiv-proof = λ y → (stream-to-Stream y , helper2 y) , λ y₁ i₁ → {!!} , {!!} }) i

-- {-# NON_TERMINATING #-}
-- zeros = in-fun {S = stream-S ℕ} (0 , λ { tt -> zeros } )

-- -- {-# NON_TERMINATING #-}
-- -- zeros2 = cons 0 zeros2


