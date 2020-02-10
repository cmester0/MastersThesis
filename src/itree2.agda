{-# OPTIONS --cubical --guardedness --safe --copatterns #-}  

module itree2 where

  open import Cubical.Foundations.Everything
  open import Cubical.Core.Everything

  open import Cubical.Data.Nat as ℕ using (ℕ)
  open import Cubical.Data.Empty
  open import Cubical.Data.Unit
  open import Cubical.Data.Bool

  open import Cubical.Data.Sum

  open import Cubical.Codata.M

  itree-tau = M ((λ _ -> Unit) , λ _ _ _ -> Unit) (tt)

  itree-ret : ∀ {ℓ} -> (Set ℓ -> Set (ℓ-suc ℓ)) -> (Set ℓ) -> Set ℓ
  itree-ret E A = A -> itree-tau

  itree-vis : ∀ {ℓ} -> (Set ℓ -> Set (ℓ-suc ℓ)) -> (Set ℓ) -> Set (ℓ-suc ℓ)
  itree-vis E A = ∀ {R} -> E R -> (R -> itree-tau) -> itree-tau 

  itree : ∀ {ℓ} -> (Set ℓ -> Set (ℓ-suc ℓ)) -> (Set ℓ) -> Set (ℓ-suc ℓ)
  itree E A = itree-ret E A ⊎ itree-vis E A

