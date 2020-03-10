{-# OPTIONS --cubical --guardedness #-} --safe

module stream where

open import M
open import Coalg

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Sigma

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

-- open import Later

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

-------------------------
-- Stream Zip function --
-------------------------

record asdf A : Set where
  field
    force : stream A

open asdf

cons-2 : ∀ {A} -> A -> asdf A -> asdf A
cons-2 = {!!}

zip : ∀ {A B} -> asdf A × asdf B -> asdf (A × B)
zip (x , y) = {!!}

  -- (zip ((record { force = tl (force x) }) , (record { force = tl (force y) })))

-- stream-eq : ∀ A -> A × stream A ≡ stream A
-- stream-eq A = isoToPath (iso (λ {(a , as) → cons a as}) (λ x → hd x , tl x) (λ b → funExt⁻ in-inverse-out b) {!!})

-- zip : ∀ {A B} -> stream A × stream B -> stream (A × B)
-- zip (x , y) = cons (hd x , hd y) (zip (tl x , tl y))

-- unzip : ∀ {A B} -> stream (A × B) -> stream A × stream B
-- unzip x = (cons (proj₁ (hd x)) (proj₁ (unzip (tl x)))) , (cons (proj₂ (hd x)) (proj₂ (unzip (tl x))))

-- zip-unzip : forall {A B} b -> zip {A = A} {B = B} (unzip b) ≡ b
-- zip-unzip = {!!}

-- unzip-zip : forall {A B} b -> unzip {A = A} {B = B} (zip b) ≡ b
-- unzip-zip = {!!}

-- zips-equality-2 : ∀ {A B} -> stream A × stream B ≡ stream (A × B)
-- zips-equality-2 = isoToPath (iso zip unzip zip-unzip unzip-zip)

-- ---------------------------------------------
-- -- Stream definitions using Later modality --
-- ---------------------------------------------

-- -- record S (A : Set) : Set where
-- --   inductive
-- --   constructor _,_
-- --   field
-- --     headS : A
-- --     tailS : ▹ (S A)

-- -- open S
