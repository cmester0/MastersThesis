{-# OPTIONS --cubical --guardedness #-} --safe

module stream where

open import M

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Later
open import Cubical.Data.List
open import Cubical.Foundations.Univalence

-- Stream example

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

-- Stream2

record S (A : Set) : Set where
  inductive
  constructor _,_
  field
    headS : A
    tailS : ▹ (S A)

open S

{-# NON_TERMINATING #-}
bisimR : ∀ (A : Set₀) -> (stream A) -> (stream A) -> Set
bisimR A xs ys = (hd xs ≡ hd ys) × bisimR A (tl xs) (tl ys)

-- bisimS : ∀ (A : Set₀) -> bisimulation (stream-S A) (bisimR A)
-- bisimS = ?

record StreamS A : Set₀ where
  coinductive
  field
    valueS : A × StreamS A

open StreamS

Head : ∀ {A} -> StreamS A -> A
Head S = (proj₁(valueS S))

Tail : ∀ {A} -> StreamS A -> StreamS A
Tail S = (proj₂(valueS S))

record Stream A : Set₀ where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

-- record Stream-to-S A (s1 : Stream A) (s2 : S A) (rel : Stream A -> ▹ S A -> Set) : Set₀ where
--   coinductive
--   field
--     head≈ : head s1 ≡ headS s2
--     tail≈ : rel (tail s1) (tailS s2)

-- asdf : Stream ≡ S
-- asdf = λ i A → ua {A = Stream A} {B = S A} ((λ x → head x , {!!}) , {!!}) i

record Stream-to-stream {A} (x : stream A) (y : Stream A) : Set where
  coinductive
  field
    head0 : hd x ≡ head y
    tail0 : Stream-to-stream (tl x) (tail y)

open Stream-to-stream

stream-to-Stream : ∀ {A} -> stream A -> Stream A
head (stream-to-Stream s) = hd s
tail (stream-to-Stream s) = stream-to-Stream (tl s)

asdd : ∀ A (x y) -> Stream-to-stream {A = A} x y → {p : stream ≡ Stream} -> PathP (λ i -> p i A) x y
asdd = λ A x y p {q} i → (transp (λ i₁ → A -> q i₁ A -> q i₁ A) i0 cons) (p .head0 i) (asdd A (tl x) (tail y) (p .tail0) i)

-- stream-to-Stream : ∀ {A} -> stream A -> Stream A
-- head (stream-to-Stream s) = hd s
-- tail (stream-to-Stream s) = stream-to-Stream (tl s)

-- {-# NON_TERMINATING #-}
-- Stream-to-stream : ∀ {A} -> Stream A -> stream A
-- Stream-to-stream {A} S = cons (head S) (Stream-to-stream {A} (tail S))

stream-equiv : ∀ {A} -> stream A ≃ Stream A -- ∀ {A} -> isEquiv (Stream-to-stream {A})
stream-equiv = stream-to-Stream , record { equiv-proof = {!!} } -- record { equiv-proof = λ y → ({!!} , {!!}) , {!!} }
