{-# OPTIONS --cubical --guardedness #-} --safe

open import M

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Data.List

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Codata.Stream

open import helper

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

--------------------------
-- Stream using M-types --
--------------------------

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

--------------------------
-- Stream using M-types --
--------------------------

open Stream

stream-to-Stream : ∀ {A} → stream A → Stream A
head (stream-to-Stream x) = (hd x)
tail (stream-to-Stream x) = (stream-to-Stream (tl x))

-- Stream-to-stream : ∀ {A} → Stream A → Chain
-- Stream-to-stream x = {!!} ,, {!!}

Stream-to-stream : ∀ {A : Set} -> Stream A -> stream A
Stream-to-stream s = Stream-to-stream (tail s)

-- Stream-to-stream : ∀ {A} → Stream A → stream A
-- Stream-to-stream x = cons (head x) (Stream-to-stream (tail x))

stream-equality : ∀ {A} -> stream A ≡ Stream A
stream-equality = isoToPath (iso (λ x → {!!}) (λ x → cons {!!} {!!}) {!!} {!!})
