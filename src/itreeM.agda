{-# OPTIONS --cubical --guardedness --copatterns #-}  

module itreeM where
  open import Cubical.Foundations.Everything
  open import Cubical.Core.Everything
  open import Cubical.Data.Nat as ℕ using (ℕ)
  open import Cubical.Data.Empty
  open import Cubical.Data.Unit
  open import Cubical.Data.Sum
  open import Cubical.Data.Sigma
  open import Cubical.Codata.M

  open import Agda.Builtin.Coinduction

  open import Later
  open import Cubical.Data.Prod   

  itree-delay : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set
  -- itree-delay E R = M ((λ _ → Unit) , (λ _ _ _ → Unit)) (λ _ _ _ → R ⊎ Unit)

  -- Definitions
  itree-delay-ret : ∀ {E R} -> itree-delay E R -> R
  itree-delay-ret r = {!!}

  itree-delay-tau : ∀ {E R} -> itree-delay E R -> itree-delay E R
  itree-delay-tau s = s .tails tt (inr tt)


  -- in the following definition we write "_" to mean "lift tt"
  -- itree-delay : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set
  -- itree-delay E R = ⟦ ((λ _ → Unit) , (λ _ _ _ → Unit)) ⟧ (λ _ → Unit ⊎ R) tt

  -- -- Definitions
  -- itree-delay-ret : ∀ {E R} -> R -> itree-delay E R
  -- itree-delay-ret r = tt , (λ y x → inr r)

  -- itree-delay-tau : ∀ {E R} -> itree-delay E R -> itree-delay E R
  -- itree-delay-tau s = tt , (λ y x → inl tt)

  -- spinD : ∀ {E R} -> itree-delay E R
  -- spinD {E = E} = itree-delay-tau {E = E} (spinD {E = E})

  --SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP SKIP

  -- itree-tree : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
  -- itree-tree E R = ⟦ ((λ _ → Lift Unit) , (λ _ _ _ → Lift Unit)) ⟧ (λ (x : {!!}) -> R ⊎ Σ Set λ (A : Set) → E A × (A → x)) {!!}
  
  -- Definitions
  -- itree-tree-ret : ∀ {E R} -> R -> itree-tree E R
  -- itree-tree-ret r = lift tt , (λ y x → inl r)

  -- itree-tree-vis : ∀ {E R} -> ∀ {A} -> E A -> (A -> itree-tree E R) -> itree-tree E R
  -- itree-tree-vis {A = A} e k = lift tt , (λ y x → inr (A , (e , k)))

  -- itree-tree : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
  -- itree-tree E R = M ((λ (x : {!!}) → R ⊎ Σ Set λ (A : Set) → E A × (A → x)) , λ x x₁ x₂ → ⊥) {!!}

  -- itree-tree-ret : ∀ {E R} -> R -> itree-tree E R
  -- head (itree-tree-ret r) = inl r
  -- tails (itree-tree-ret r) = λ y x → {!!}



  -- itree : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
  -- itree E R = M ((λ _ → Lift Unit) , (λ _ (x : Lift Unit) _ → Unit ⊎ (R ⊎ Σ Set λ (A : Set) → E A × (A → x)))) (lift tt)

  -- Tau : ∀ {E R} -> itree E R -> itree E R
  -- Tau t = t .tails _ (inl tt)
  
