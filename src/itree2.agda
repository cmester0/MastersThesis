{-# OPTIONS --cubical --guardedness --copatterns #-}  --safe 

module itree2 where

  open import Cubical.Foundations.Everything
  open import Cubical.Core.Everything

  open import Cubical.Data.Nat as ℕ using (ℕ)
  open import Cubical.Data.Empty
  open import Cubical.Data.Unit
  open import Cubical.Data.Bool
  open import Cubical.Data.Prod
  open import Cubical.Data.Sum

  open import Cubical.Codata.M

  open import Later

  _⊛_⊛_ : ∀ {ℓ} {A B C : Set ℓ} -> ▹ (A -> B -> C) -> ▹ A -> ▹ B -> ▹ C
  _⊛_⊛_ f a b = (f ⊛ a) ⊛ b

  data itree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
    Ret : R -> itree E R
    Tau : ▹ (itree E R) -> itree E R
    Vis : ∀ {A} -> E A -> (A -> ▹ itree E R) -> itree E R

  -- itree operations
  trigger : ∀ {E : Set₀ -> Set₁} {A : Set₀} -> E A -> itree E A
  trigger e = Vis e (next ∘ Ret)

  -- Monadic operations
  bind-pre : ∀ {E R S} -> ▹ (itree E R -> (R -> itree E S) -> itree E S) -> itree E R -> (R -> itree E S) -> itree E S
  bind-pre bind (Ret r) k = k r
  bind-pre bind (Tau t) k = Tau ((bind ⊛ t) ⊛ next k)
  bind-pre bind (Vis {A = A} e f) k = Vis e (λ (x : A) → bind ⊛ (f x) ⊛ next k)

  bind : ∀ {E R S} -> itree E R -> (R -> itree E S) -> itree E S
  bind = fix bind-pre

  bind' : ∀ {E R S} -> itree E R -> (R -> itree E S) -> itree E S
  bind' = bind-pre (next bind)

  bind-unfold : ∀ {E R S} -> bind {E = E} {R = R} {S = S} ≡ bind-pre (next bind)
  bind-unfold = fix-eq bind-pre
  
  -----------------------------
  -- Equality / Bisimularity --
  -----------------------------

  -- Equality
  data _≅_ {E} {R : Set₀} : (itree E R -> itree E R -> Set₁) where
    EqRet : (a b : R) -> a ≡ b -> (Ret a) ≅ (Ret b)
    EqTau : (t1 t2 : itree E R) -> t1 ≅ t2 -> (Tau (next t1)) ≅ (Tau (next t2))
    EqVis : {A : _} -> (e : E A) -> (k1 k2 : A -> ▹ (itree E R)) -> k1 ≡ k2 -> (Vis e k1) ≅ (Vis e k2)

  -- bisimularity
  bisim : ∀ {E R} -> {r s : itree E R} -> r ≅ s -> r ≡ s
  bisim (EqRet _ _ p) = λ i → Ret (p i)
  bisim (EqTau t1 t2 p) = λ i → Tau (next (bisim p i)) -- r = t1, s = t2
  bisim (EqVis e k1 k2 p) = λ i → Vis e (p i)

  TODO0 : ∀ {E R} -> {r s : R} -> Ret {E = E} r ≡ Ret s -> r ≡ s
  TODO0 = {!!}

  misib : ∀ {E R} -> {r s : itree E R} -> r ≡ s -> r ≅ s
  misib {r = Ret r} {s = Ret s} p = EqRet r s (TODO0 p)
  misib {r = Tau t1} {s = Tau t2} p = {!!}
  misib {r = Ret r} {s = Ret s} p = {!!}
  

  -- postulate
  --   misib : ∀ {E R} -> {r s : itree E R} -> r ≡ s -> r ≅ s

  -- iso1 : {A : Type₀} → {x y : stream A} → (p : x ≡ y) → bisim (misib p) ≡ p
  -- head  (iso1 p i j)       = stream-hd (p j)
  -- tails (iso1 p i j) tt tt = iso1 (λ i → stream-tl (p i)) i j

  iso2 : ∀ {E R} → {x y : itree E R} → (p : x ≅ y) → misib (bisim p) ≡ p
  iso2 (EqRet r s p) = λ i → {!!}
  iso2 (EqVis e k1 k2 p) = {!!}
  iso2 (EqTau t1 t2 p) = {!!}

  -- path≃bisim : ∀ {E R} → {x y : itree E R} → (x ≡ y) ≃ (x ≅ y)
  -- path≃bisim = isoToEquiv (iso misib bisim iso2 iso1)

  -- path≡bisim : {A : Type₀} → {x y : stream A} → (x ≡ y) ≡ (x ≈ y)
  -- path≡bisim = ua path≃bisim


  itree-≅-tau : ∀ {E R} (t1 t2 : ▹ itree E R) -> t1 ≡ t2 -> Tau t1 ≡ Tau t2
  itree-≅-tau t1 t2 p = λ i -> funExt⁻ {f = Tau} {g = Tau} refl (p i) i


  -- TODO'S:
  postulate
    sim_convert : ∀ {E A B} {R : Set₀} -> ▹ (itree E A -> itree E B -> Set₁) -> (R -> ▹ itree E A) -> (R -> ▹ itree E B) -> Set₁
    -- sim_convert = ∀ (v : R) -> sim ⊛ (k1 v) ⊛ (k2 v)
    -- sim_convert = (transp k1) ≡ k2

    k1k2 : ∀ {E A} {R : Set₀} -> (f : R -> ▹ itree E A) -> (sim : ▹ (itree E A → itree E A → Set₁)) -> sim_convert sim f f

  -- Equality
  data euttF {E} {A B : Set₀} {r : A -> B -> Set₀} (sim : ▹ (itree E A -> itree E B -> Set₁)) : (itree E A -> itree E B -> Set₁) where
    EqRet : (a : A) -> (b : B) -> (REL : r a b) -> euttF sim (Ret a) (Ret b)
    EqVis : {R : Set₀} -> (e : E R) -> (k1 : R -> ▹ (itree E A)) -> (k2 : R -> ▹ (itree E B)) -> (REL : sim_convert sim k1 k2) -> euttF sim (Vis e k1) (Vis e k2)
    EqTau : (t1 : itree E A) -> (t2 : itree E B) -> euttF sim (Tau (next t1)) (Tau (next t2)) -- -> (REL : sim t1 t2)
    EqTauL : (t1 : itree E A) -> (ot2 : itree E B) -> (REL : euttF {r = r} sim t1 ot2) -> euttF sim (Tau (next t1)) ot2
    EqTauR : (ot1 : itree E A) -> (t2 : itree E B) -> (REL : euttF {r = r} sim ot1 t2) -> euttF sim ot1 (Tau (next t2))
  
  -- k1k2m : ∀ {E A B} {R : Set₀} -> (k1 : R -> ▹ itree E A) (k2 : R -> ▹ itree E B) -> (p : A ≡ B) -> PathP (λ x → R → ▹ itree E (p x)) k1 k2
  -- k1k2m = λ k1 k2 p x x₁ x₂ → {!!}

  eutt : ∀ {E R S} (rel : R -> S -> Set₀) -> itree E R -> itree E S -> Set₁
  eutt rel = fix (euttF {r = rel})

  _≈_ : ∀ {E} {R}  -> itree E R -> itree E R -> Set₁
  _≈_ {R = R} = eutt _≡_

  _≈'_ : ∀ {E : Set₀ -> Set₁} {R : Set₀}  -> (itree E R -> itree E R -> Set₁)
  _≈'_ {E = E} {R = R} = euttF {r = _≡_} (next _≈_)

  fix-unfold : ∀ {E R S} (rel : R -> S -> Set₀) -> eutt {E} {R} {S} rel ≡ euttF {E} {R} {S} {r = rel} (next (eutt rel))
  fix-unfold rel = fix-eq euttF

  ≈unfold : ∀ {E R} -> _≈_ {E = E} {R = R} ≡ _≈'_
  ≈unfold = fix-eq euttF

  -- rewrites : ∀ b c -> b ≈ c -> b ≈' c
  -- rewrites b c p = {!!}  

  -- rewrites : ∀ {E} {R} (x y : itree E R) -> x ≈' y -> x ≈ y
  -- rewrites x y (EqRet a b p) = cong (λ x → {!!}) p {!!}

  -- bisimularity
  -- bisim≈ : ∀ {E R} -> (r s : itree E R) -> r ≈' s -> r ≡ s
  -- bisim≈ r s (EqRet _ _ p) = λ i → Ret (p i)
  -- bisim≈ r s (EqVis e k1 k2 p) = λ i → Vis e {!!}
  -- bisim≈ r s (EqTau t1 t2) = λ i → Tau (next (bisim t1 t2 {!!} i))

  ------------------------------
  -- Properties of definition --
  ------------------------------

  -- Monad Laws

  -- itree-M1 : ∀ {E R} (k : R -> itree E R) (v : R) -> bind' (Ret v) k ≅ k v
  -- itree-M1 k v = {!!}

  -- itree-M2 : ∀ {E R} (t : itree E R) -> bind' t Ret ≅ t
  -- itree-M2 (Ret r) = EqRet r r refl
  -- itree-M2 (Tau t) = {!!}
  -- itree-M2 (Vis e f) = {!!}

  -- itree-M3 : ∀ {E R} (k : R -> itree E R) (v : R) -> (k v) ≅ (bind' (Ret v) k)
  -- itree-M3 k v = {!!}
  
  -- Congruence

  -- itree-≅-tau : ∀ {E R} (t1 t2 : itree E R) -> t1 ≅ t2 -> Tau (next t1) ≅ Tau (next t2)
  -- itree-≅-tau t1 t2 p  = EqTau t1 t2 p

  -- itree-≅-next-tau : ∀ {E R} (t1 t2 : ▹ itree E R) -> t1 ≡ t2 -> Tau t1 ≅ Tau t2
  -- itree-≅-next-tau t1 t2 p  = EqTau t1 t2 p
  

  -- Equality relations
  -- ≅refl : ∀ {E R} (t : itree E R) -> t ≅ t
  -- ≅refl (Ret r) = EqRet r r refl
  -- ≅refl (Tau t) = {!!}
  -- ≅refl (Vis e f) = {!!}


  -- itree-≈refl : ∀ {E R} (t : itree E R) -> t ≈' t
  -- itree-≈refl (Ret r) = EqRet r r refl
  -- itree-≈refl (Tau n) = EqTau ? ?
  -- itree-≈refl (Vis e f) = EqVis e f f (k1k2 f λ x → fix euttF)

  -- itree-≈tau-pre : ∀ {E R} (t : itree E R) -> (Tau (next t)) ≈' t
  -- itree-≈tau-pre t = EqTauL t t (itree-≈refl t)

  -- itree-≈tau : ∀ {E R} (t : itree E R) -> (Tau (next t)) ≈ t
  -- itree-≈tau (Ret r) = itree-≈tau-pre (Ret r)


    -- EqTauL : (t1 : itree E A) -> (ot2 : itree E B) -> (REL : euttF {r = r} sim t1 ot2) -> euttF sim (Tau (next t1)) ot2

  -- itree-≈tau : ∀ {E R} (t : itree E R) -> Tau (next t) ≈ t
  -- itree-≈tau (Ret r) = {!!}

  asdf : ∀ {E} {R} {t1 t2 : itree E R} {k1 k2 : R -> itree E R} -> t1 ≅ t2 -> (∀ x -> k1 x ≅ k2 x) -> bind t1 k1 ≅ bind t2 k2
  asdf p q = {!!}

  -- Examples
  data IO : Type₀ → Type₁ where
    Input : IO ℕ
    Output : (x : ℕ) -> IO Unit

  -- Spin definition
  spin-pre : ▹ itree IO ⊥ -> itree IO ⊥
  spin-pre spin = Tau spin

  spin : itree IO ⊥
  spin = fix spin-pre

  spin-unroll : spin ≡ spin-pre (next spin)
  spin-unroll = fix-eq spin-pre

  -- Echo definition
  echo-pre : ▹ itree IO ⊥ -> itree IO ⊥
  echo-pre echo = fix λ y -> (Vis Input λ x -> next (Vis (Output x) λ _ → next (Tau echo)))

  echo : itree IO ⊥
  echo = fix echo-pre

  echo-unroll : echo ≡ echo-pre (next echo)
  echo-unroll = fix-eq echo-pre

  -- Echo definition trigger
  echo2-pre : ▹ itree IO ⊥ -> itree IO ⊥
  echo2-pre echo2 = bind (trigger Input) λ x -> bind (trigger (Output x)) λ _ → Tau echo2

