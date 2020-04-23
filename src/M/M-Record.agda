{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat.Algebra

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun ; _∘_)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.HLevels

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding

open import helper
open import Container
open import Coalg.Base
-- open import Cubical.Codata.M
open import M.Base

module M.M-Record where

record M-2 (C : Container) : Type₀ where
  coinductive
  field
    head : C .fst
    tails : C .snd head → M-2 C

open M-2

M-to-M-2 : {S : Container} → M S → M-2 S
head (M-to-M-2 m) = out-fun m .fst
tails (M-to-M-2 m) x = M-to-M-2 (out-fun m .snd x)

M-2-to-M-x : {S : Container} → M-2 S → (n : ℕ) → W S n
M-2-to-M-x m 0 = lift tt
M-2-to-M-x m (suc n) = head m , λ x → M-2-to-M-x m n

M-2-to-M-π : {S : Container} → (m : M-2 S) → (n : ℕ) → πₙ S (M-2-to-M-x m (suc n)) ≡ M-2-to-M-x m n
M-2-to-M-π m 0 i = lift tt
M-2-to-M-π m (suc n) i = head m , λ x → M-2-to-M-π m n i

M-2-to-M : {S : Container} → M-2 S → M S
M-2-to-M m = M-2-to-M-x m , M-2-to-M-π m

postulate
  M-to-M-2-section : ∀ {S} (b : M-2 S) → M-to-M-2 (M-2-to-M b) ≡ b
-- head (M-to-M-2-section b i) = head b
-- tails (M-to-M-2-section {S} b i) x =
--   (tails (M-to-M-2 (M-2-to-M b)) x
--     ≡⟨ refl ⟩
--   M-to-M-2 ((λ n → transport (refl {x = W S n}) (M-2-to-M-x b n)) , (λ n i → (transport (λ i → α-iso-step-5-Iso-helper1 (λ n → head b) (λ n i → head b) (λ n x → M-2-to-M-x b n) n i) (λ i x → M-2-to-M-π b n i)) i x))
--     ≡⟨ refl ⟩
--   M-to-M-2 ((λ n → transport (refl {x = W S n}) (M-2-to-M-x b n)) , (λ n i → (transport (λ i → α-iso-step-5-Iso-helper1 (λ n → head b) (λ n i → head b) (λ n x → M-2-to-M-x b n) n i) (λ i x → M-2-to-M-π b n i)) i x))
--     ≡⟨ cong M-to-M-2 (ΣPathP (transportRefl (M-2-to-M-x b) , {!!})) ⟩
--   M-to-M-2 ((λ n → M-2-to-M-x b n) , (λ n → M-2-to-M-π b n))
--     ≡⟨ {!!} ⟩
--   M-to-M-2 (M-2-to-M-x b , M-2-to-M-π b)
--     ≡⟨ M-to-M-2-section b ⟩
--   b
--     ≡⟨ {!!} ⟩ -- is the tail equal to b?
--   tails b x ∎) i

postulate
  M-to-M-2-retraction : ∀ {S} (a : M S) → M-2-to-M (M-to-M-2 a) ≡ a
-- M-to-M-2-retraction {S} a =
--   M-2-to-M (M-to-M-2 a)
--     ≡⟨ refl ⟩
--   (M-2-to-M-x (M-to-M-2 a) , M-2-to-M-π (M-to-M-2 a))
--     ≡⟨ {!!} ⟩
--   ((λ {0 → lift tt ; (suc n) → (out-fun a .fst) , λ x → M-2-to-M-x (M-to-M-2 a) n}) ,
--     λ {0 → refl {x = lift tt} ; (suc n) → λ i → (out-fun a .fst) , λ x → M-2-to-M-π (M-to-M-2 a) n i})
--     ≡⟨ {!!} ⟩
--   ((λ {0 → lift tt ; (suc n) → (out-fun a .fst) , λ x → M-2-to-M-x (M-to-M-2 a) n}) ,
--     λ {0 → refl {x = lift tt} ; (suc n) → λ i → (out-fun a .fst) , λ x → M-2-to-M-π (M-to-M-2 a) n i})
--     ≡⟨ {!!} ⟩
--   a ∎

M-equality : ∀ S → M S ≡ M-2 S
M-equality = λ S → isoToPath (iso M-to-M-2 M-2-to-M M-to-M-2-section M-to-M-2-retraction)
