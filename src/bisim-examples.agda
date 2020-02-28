{-# OPTIONS --cubical --guardedness #-} --safe
module bisim-examples where

open import itree
-- open import itree2
open import M
-- open import itree-examples
-- open import Coalg

open import Cubical.Data.Unit
-- open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
-- open import Cubical.Data.Empty
-- open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Id using (∥_∥)
open import Cubical.Foundations.Univalence
-- open import Cubical.Core.Glue

open import Cubical.HITs.SetQuotients

open import Cubical.Codata.Stream

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

record stream-bisim {A} (x y : stream A) : Set where
  coinductive
  field
    hd≈ : hd x ≡ hd y
    tl≈ : stream-bisim (tl x) (tl y)

open Stream

stream-to-Stream : ∀ {A} -> stream A -> Stream A
head (stream-to-Stream x) = hd x
tail (stream-to-Stream x) = stream-to-Stream (tl x)

{-# NON_TERMINATING #-}
Stream-to-stream' : ∀ {A} -> Stream A -> stream A
Stream-to-stream' x = cons (head x) (Stream-to-stream' (tail x))

Stream-to-stream : ∀ {A} -> Stream A -> stream A
Stream-to-stream x = cons (head x) (Stream-to-stream' (tail x))

helper : ∀ {A} x -> stream-to-Stream {A} (Stream-to-stream x) ≡ x
helper x = λ i → {!!}

helper2 : ∀ {A} x -> Stream-to-stream {A} (stream-to-Stream x) ≡ x
helper2 x = λ i → {!!}

-- stream-equiv : stream ≡ Stream
-- stream-equiv i A = ua {A = stream A} {B = Stream A} ( stream-to-Stream , record { equiv-proof = λ y → (Stream-to-stream y , helper y) , λ y₁ i₁ → {!!} , {!!} }) i

stream-equiv2 : Stream ≡ stream
stream-equiv2 i A = ua {A = Stream A} {B = stream A} ( Stream-to-stream , record { equiv-proof = λ y → (stream-to-Stream y , helper2 y) , λ y₁ i₁ → {!!} , {!!} }) i


{-# NON_TERMINATING #-}
zeros = in-fun {S = stream-S ℕ} (0 , λ { tt -> zeros } )

-- {-# NON_TERMINATING #-}
-- zeros2 = cons 0 zeros2


data delay≈ {R} : (delay R) -> (delay R) -> Set where
  EqPNow : ∀ r s -> r ≡ s -> delay≈ (delay-ret r) (delay-ret s)
  EqPLater : ∀ t u -> delay≈ t u -> delay≈ (delay-tau t) (delay-tau u)

data weak-delay≈ {R} : (delay R) -> (delay R) -> Set where
  EqNow : ∀ r s -> r ≡ s -> weak-delay≈ (delay-ret r) (delay-ret s)
  EqLater : ∀ t u -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) (delay-tau u)
  EqLaterL : ∀ t u -> weak-delay≈ t u -> weak-delay≈ (delay-tau t) u
  EqLaterR : ∀ t u -> weak-delay≈ t u -> weak-delay≈ t (delay-tau u)

-- isEmbedding -- TODO!

asdf : ∀ {R} -> delay R -> delay R / weak-delay≈
asdf = [_]

{-# NON_TERMINATING #-}
spin3 : ∀ {R} -> delay R
spin3 {R} = delay-tau {R = R} spin3

k : asdf {R = ℕ} (delay-tau {R = ℕ} (delay-ret {R = ℕ} 2)) ≡ asdf {R = ℕ} (delay-ret {R = ℕ} 2)
k = λ i → eq/ (delay-tau {R = ℕ} (delay-ret {R = ℕ} 2)) (delay-ret {R = ℕ} 2) (EqLaterL (delay-ret {R = ℕ} 2) (delay-ret {R = ℕ} 2) (EqNow 2 2 refl)) i

-- as : (zeros2 ≈ zeros2)
-- head≈ as = refl
-- tails≈ as = λ pa pb → {!!}

-- asd : ∀ {R} -> isContr (Σ (delay R) λ x -> x ≡ delay-tau x)
-- asd = ({!!} , {!!}) , (λ y i → {!!} , (λ i₁ → {!!} , {!!}))

-- bisim-helper : ∀ {ℓ} {S : Container {ℓ}} -> bisimulation S M-coalg _≡_
-- bisim-helper {S = S} = record { αᵣ = λ x -> let b = (out-fun {S = S} (fst x)) in {!!} , {!!} ; rel₁ = λ i a → {!!} ; rel₂ = refl }

-- Σ (S .fst) λ x → (S .snd x) -> X

-- data delay≈ {R} : delay R -> delay R -> Set where
--   EqNow : ∀ r s -> r ≡ s -> delay≈ (delay-ret r) (delay-ret s)
--   EqLater : ∀ t u -> delay≈ t u -> delay≈ (delay-tau t) (delay-tau u)

-- asdf' : ∀ {R} -> bisimulation (delay-S R) M-coalg delay≈
-- -- αᵣ asdf' = {!!}
-- rel₁ (asdf' {R = R}) i ((a , c) , b , EqNow r s p) = {!!}
-- rel₁ (asdf' {R = R}) i (a , b , EqLater _ _ _) = {!!}
-- -- rel₂ asdf' = {!!}

-- data delayP≈ {R} : (P₀ {S = delay-S R} (delay R)) -> (P₀ {S = delay-S R} (delay R)) -> Set where
--   EqPNow : ∀ r s -> r ≡ s -> delayP≈ (inr r , λ ()) (inr s , λ ())
--   EqPLater : ∀ t u -> delayP≈ (out-fun t) (out-fun u) -> delayP≈ (inl tt , λ _ → t) (inl tt , λ _ → u)

-- asdf : ∀ {R} -> bisimulation (delay-S R) PM-coalg delayP≈
-- αᵣ asdf = λ x -> (x .snd .fst .fst) , λ x₁ → x
-- rel₁ (asdf {R = R}) i ((a , b) , (c , d) , EqPNow _ _ p) = (inr (p i)) , λ x → ({!!} , {!!}) -- (P₀ (M S))
-- rel₁ asdf i (a , b , EqPLater _ _ p) = {!!}
-- rel₂ asdf = {!!}

-- data itree≈ {E} {R} : itree E R -> itree E R -> Set₁ where
--   EqRet : ∀ r s -> r ≡ s -> itree≈ (ret r) (ret s)
--   EqTau : ∀ t u -> itree≈ t u -> itree≈ (tau t) (tau u)
--   EqVis : ∀ {A} e k1 k2 -> k1 ≡ k2 -> itree≈ (vis {A = A} e k1) (vis {A = A} e k2)

-- open itree≈

-- -- ((Unit ⊎ R) ⊎ Σ Set E) -,- (λ { (inl (inl _)) -> Lift Unit ; (inl (inr _)) -> ⊥₁ ; (inr (A , e)) -> Lift A } )
-- itree-bisim : ∀ {E : Set₀ -> Set₁} {R : Set₀} -> bisimulation (itree-S E R) M-coalg
-- R itree-bisim = itree≈
-- αᵣ (itree-bisim {E} {R}) = {!!}
-- rel₁ itree-bisim = λ i → λ a → {!!}
-- rel₂ itree-bisim = {!!}

-- spin-it : itree IO ℕ
-- spin-it = vis Input (λ x -> tau (ret x))

-- spin-it-eq : spin-it ≡ spin-it
-- spin-it-eq = coinduction (itree-S IO ℕ) itree-bisim spin-it spin-it (EqVis {!!} {!!} {!!} {!!})

-- -- delay examples
-- data delay≈ {R} : delay R -> delay R -> Set where
--   delay-ret≈ : (r s : R) -> r ≡ s -> delay≈ (delay-ret r) (delay-ret s)
--   delay-tau≈ : (t u : delay R) -> delay≈ t u -> delay≈ (delay-tau t) (delay-tau u)

-- open delay≈

-- delay-bisim : ∀ {R} -> bisimulation (delay-S R) M-coalg
-- R delay-bisim = delay≈
-- αᵣ delay-bisim = {!!}
-- rel₁ delay-bisim = {!!}
-- rel₂ delay-bisim = {!!}

-- ret2≡ret3 : ret2 ≡ ret3
-- ret2≡ret3 = coinduction (delay-S ℕ) delay-bisim ret2 ret3 (delay-tau≈ (delay-ret 2) (delay-ret 2) (delay-ret≈ 2 2 refl))

-- spin≡spin : ∀ {R} -> spin {R} ≡ spin
-- spin≡spin {R = R} = coinduction (delay-S R) delay-bisim spin spin (delay-tau≈ spin spin {!!})
