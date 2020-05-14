{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma hiding (_×_)
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
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding

open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.Coalg

module M.Base where

----------------------------------------
-- Property of functions into M-types --
----------------------------------------

-- out-lift-to-M :
--   ∀ {ℓ} {A : Set ℓ} {S : Container {ℓ}}
--   → (lift-x : (n : ℕ) -> A → X (sequence S) n)
--   → (lift-π : (n : ℕ) → (a : A) →  π (sequence S) (lift-x (suc n) a) ≡ lift-x n a)
--   → (s : A)
--   → out-fun (lift-to-M lift-x lift-π s)
--   ≡ ((lift-x (suc 0) s .fst) , (λ z → (λ n → (subst (λ k → (n : ℕ) → k n) (funExt λ n → cong (λ k → S .snd k → W S n) (α-iso-step-5-Iso-helper0 {S = S} (λ n → lift-x (suc n) s .fst) ((λ n i → lift-π (suc n) s i .fst)) n)) (λ n → lift-x (suc n) s .snd)) n z) , (λ n → funExt⁻ ((subst (λ k → (n : ℕ) → k n) (funExt λ n → α-iso-step-5-Iso-helper1 (λ n → lift-x (suc n) s .fst) (λ n i → lift-π (suc n) s i .fst) (λ n → lift-x (suc n) s .snd) n) (λ n i → lift-π (suc n) s i .snd)) n) z)))
-- out-lift-to-M {S = S} lift-x lift-π s = refl

lift-x-general :
  ∀ {ℓ} {S : Container ℓ}
  → (ℕ → S .fst) → (n : ℕ) -> Wₙ S n
lift-x-general _ 0 = lift tt
lift-x-general f (suc n) = f n , λ x → lift-x-general f n

lift-π-general :
  ∀ {ℓ} {S : Container ℓ}
  (f : ℕ → S .fst) → (∀ n → f (suc n) ≡ f n) → (n : ℕ) → πₙ S (lift-x-general f (suc n)) ≡ lift-x-general f n
lift-π-general _ k 0 = refl {x = lift tt}
lift-π-general f k (suc n) i = k n i , λ x → lift-π-general f k n i

lift-to-M-general : ∀ {ℓ} {S : Container ℓ}
  → (x :  ℕ → S .fst)
  → (π : ∀ n → x (suc n) ≡ x n)
  ---------------
  → (M S)
lift-to-M-general x π = lift-x-general x , lift-π-general x π
