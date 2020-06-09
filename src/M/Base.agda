{-# OPTIONS --cubical --guardedness --safe #-}

-- Construction of M-types from
-- https://arxiv.org/pdf/1504.02949.pdf
-- "Non-wellfounded trees in Homotopy Type Theory"
-- Benedikt Ahrens, Paolo Capriotti, Régis Spadotti

module M.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Nat.Algebra

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sum

open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Container

open import Cubical.Codata.M.AsLimit.Coalg.Base
open import Cubical.Codata.M.AsLimit.M.Base public

open Iso

-- Lemma 10
-- https://arxiv.org/pdf/1504.02949.pdf
-- "Non-wellfounded trees in Homotopy Type Theory"
-- Benedikt Ahrens, Paolo Capriotti, Régis Spadotti

lemma10-Iso : ∀ {ℓ} {S : Container ℓ} (C,γ : Coalg₀ {S = S}) -> Iso (C,γ .fst -> M S) (Cone C,γ)
fun (lemma10-Iso _) f = (λ n z → (f z) .fst n) , λ n i a → (f a) .snd n i
inv (lemma10-Iso _) (u , q) z = (λ n → u n z) , λ n i → q n i z
rightInv (lemma10-Iso _) _ = refl
leftInv (lemma10-Iso _) _ = refl
