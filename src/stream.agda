{-# OPTIONS --cubical --guardedness #-} --safe

module stream where

open import M

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

-- Stream example

stream-S : ∀ A -> Container
stream-S A = (A -,- (λ _ → Unit))

stream : ∀ (A : Set₀) -> Set₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

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

stream-to-Stream : ∀ {A} -> stream A -> Stream A
head (stream-to-Stream s) = hd s
tail (stream-to-Stream s) = stream-to-Stream (tl s)

{-# NON_TERMINATING #-}
Stream-to-stream : ∀ {A} -> Stream A -> stream A
Stream-to-stream {A} S = cons (head S) (Stream-to-stream {A} (tail S))

stream-equiv : ∀ {A} -> isEquiv (stream-to-Stream {A})
stream-equiv = {!!}
