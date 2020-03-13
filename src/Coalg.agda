{-# OPTIONS --cubical --guardedness #-} --safe

open import M

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )

open import Cubical.Data.Unit

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Id using (ap ; _∙_)
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import helper

open import Cubical.Data.Sigma

module Coalg where

open import Coalg.Base public
open import Coalg.Properties public
