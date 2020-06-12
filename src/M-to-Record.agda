{-# OPTIONS --cubical --guardedness --safe #-}

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

open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.Coalg.Base
open import Cubical.Codata.M renaming (M to M-2)
open import M.Base

module M-to-Record where

Container→IxCont : ∀ {ℓ} → Container ℓ → IxCont {ℓ} (Lift Unit)
Container→IxCont = λ x → (λ {(lift tt) → x .fst}) , (λ {(lift tt) k (lift tt) → x .snd k})

open M-2

M-to-M-2 : ∀ {ℓ} {S : Container ℓ} → M S → M-2 (Container→IxCont S) (lift tt)
head (M-to-M-2 m) = out-fun m .fst
tails (M-to-M-2 m) (lift tt) x = M-to-M-2 (out-fun m .snd x)

private
  M-2-to-M-x : ∀ {ℓ} {S : Container ℓ} → M-2 (Container→IxCont S) (lift tt) → (n : ℕ) → Wₙ S n
  M-2-to-M-x m 0 = lift tt
  M-2-to-M-x m (suc n) = head m , λ x → M-2-to-M-x (tails m (lift tt) x) n

  M-2-to-M-π : ∀ {ℓ} {S : Container ℓ} → (m : M-2 (Container→IxCont S) (lift tt)) → (n : ℕ) → πₙ S (M-2-to-M-x m (suc n)) ≡ M-2-to-M-x m n
  M-2-to-M-π m 0 i = lift tt
  M-2-to-M-π m (suc n) i = head m , λ x → M-2-to-M-π (tails m (lift tt) x) n i

M-2-to-M : ∀ {ℓ} {S : Container ℓ} → M-2 (Container→IxCont S) (lift tt) → M S
M-2-to-M {ℓ} {S} m = M-2-to-M-x m , M-2-to-M-π m

postulate
  M-2-to-M-out : ∀ {ℓ} {S : Container ℓ} (b : M-2 (Container→IxCont S) (lift tt)) x → out-fun (M-2-to-M b) .snd x ≡ M-2-to-M (out (lift tt) b .snd (lift tt) x)

{-# TERMINATING #-} -- Should be non-terminating ?, however head case is terminating
M-to-M-2-section : ∀ {ℓ} {S : Container ℓ} (b : M-2 (Container→IxCont S) (lift tt)) → M-to-M-2 (M-2-to-M b) ≡ b
head (M-to-M-2-section b i) = head b
tails (M-to-M-2-section {S = S} b i) (lift tt) x =
  (M-to-M-2 (out-fun (M-2-to-M b) .snd x)
    ≡⟨ cong M-to-M-2 (M-2-to-M-out b x) ⟩
  M-to-M-2 (M-2-to-M (out (lift tt) b .snd (lift tt) x))
    ≡⟨ M-to-M-2-section (out (lift tt) b .snd (lift tt) x) ⟩
  tails b (lift tt) x ∎) i

private
  postulate
    limit-def : ∀ {ℓ} {S : Container ℓ} (a : M S) n → (out-fun a .fst , (λ x → fst (out-fun a .snd x) n)) ≡ fst a (suc n)
    
  M-to-M-2-retraction-x : ∀ {ℓ} {S : Container ℓ} (a : M S) n → M-2-to-M-x (M-to-M-2 a) n ≡ fst a n
  M-to-M-2-retraction-x a 0 = refl
  M-to-M-2-retraction-x a (suc n) =
    (head (M-to-M-2 a) , λ x → M-2-to-M-x (tails (M-to-M-2 a) (lift tt) x) n)
      ≡⟨ refl ⟩
    (out-fun a .fst , λ x → M-2-to-M-x (M-to-M-2 (out-fun a .snd x)) n)
      ≡⟨ ΣPathP (refl , funExt λ x → M-to-M-2-retraction-x (out-fun a .snd x) n) ⟩
    (out-fun a .fst , λ x → fst (out-fun a .snd x) n)
      ≡⟨ limit-def a n ⟩
    fst a (suc n) ∎

  postulate
    M-to-M-2-retraction-π :
      ∀ {ℓ} {S : Container ℓ} (a : M S) n
      → PathP (λ i → π (sequence S) (funExt (M-to-M-2-retraction-x a) i (suc n)) ≡ funExt (M-to-M-2-retraction-x a) i n)
              (M-2-to-M-π (M-to-M-2 a) n)
              (snd a n)
  
M-to-M-2-retraction : ∀ {ℓ} {S : Container ℓ} (a : M S) → M-2-to-M (M-to-M-2 a) ≡ a
M-to-M-2-retraction a =
  M-2-to-M (M-to-M-2 a)
    ≡⟨ refl ⟩
  M-2-to-M-x (M-to-M-2 a) , M-2-to-M-π (M-to-M-2 a)
    ≡⟨ ΣPathP (funExt (M-to-M-2-retraction-x a) , λ i n → M-to-M-2-retraction-π a n i) ⟩
  a ∎

M-equality : ∀ {ℓ} {S : Container ℓ} → M S ≡ M-2 (Container→IxCont S) (lift tt)
M-equality = isoToPath (iso M-to-M-2 M-2-to-M M-to-M-2-section M-to-M-2-retraction)
