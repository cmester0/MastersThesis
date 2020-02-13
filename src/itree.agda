{-# OPTIONS --cubical --guardedness --copatterns #-}  

module itree where
  open import Cubical.Foundations.Everything
  open import Cubical.Core.Everything
  open import Cubical.Data.Nat as ℕ using (ℕ)
  open import Cubical.Data.Empty
  open import Cubical.Data.Unit
  open import Cubical.Codata.M

  open import Agda.Builtin.Coinduction

  open import Later
  open import Cubical.Data.Prod

  data itreeF {E : Set₀ -> Set₁} {R : Set₀} (itree : Set₁) : Set₁ where
    RetF : (r : R) -> itreeF itree
    TauF : (t : itree) -> itreeF itree
    VisF : {X : Set₀} -> (e : E X) -> (k : X -> itree) -> itreeF itree

  record itree (E) (R) : Set₁ where
    coinductive
    constructor go
    field
      observe-pre : itreeF {E} {R} (itree E R)

  open itree

  itree' : ∀ E R -> Set₁
  itree' E R = itreeF {E} {R} (itree E R)

  observe : ∀ {E R} -> itree E R -> itree' E R
  observe t = observe-pre t

  Ret : ∀ {E} {R} → R -> itree E R
  Ret x = go (RetF x)

  Tau : ∀ {E} {R} → itree E R -> itree E R
  Tau t = go (TauF t)

  Vis : ∀ {E} {R} → ∀ {A} -> E A -> (A -> itree E R) -> itree E R
  Vis e k = go (VisF e k)

  -- Bind

  -- bind-pre : ∀ {E T U} -> (itree E T -> itree E U) -> itreeF {E} {T} (itree E T) -> {k : T -> itree E U} -> itree E U
  -- bind-pre bind (RetF r) {k = k} = k r
  -- bind-pre bind (TauF t) = Tau (bind t)
  -- bind-pre bind (VisF e f) = Vis e (λ x → bind (f x))

  bind-pre : ∀ {E T U} -> (itree E T -> itree E U) -> itreeF {E} {T} (itree E T) -> {k : T -> itree E U} -> itree E U
  bind-pre bind (RetF r) {k = k} = k r
  bind-pre bind (TauF t) = Tau (bind t)
  bind-pre bind (VisF e f) = Vis e (λ x → bind (f x))

  -- record bind {E T U} : Set₁ where
  --   coinductive
  --   field
  --     bind' : itree E T -> itree E U

  bind' : ∀ {E T U} -> itree E T -> {k : T -> itree E U} -> itree E U
  bind' t = fix λ x -> bind-pre (λ x₁ → {!!}) (observe t)

  -- Examples
  
  -- Examples
  data IO : Type₀ → Type₁ where
    Input : IO ℕ
    Output : (x : ℕ) -> IO Unit

  -- Spin definition
  spin-pre : itree IO ⊥
  spin-pre = Tau spin-pre

