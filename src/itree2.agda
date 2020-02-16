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

  -- -- Equality
  -- record _,_≅_ {E} {R S : Set₀} (p : R ≡ S) (_ : itree E R) (_ : itree E S) : Set₁ where
  --   inductive
  --   field
  --     EqRet : (a : R) (b : S) -> PathP (λ i -> p i) a b
  --     EqTau : (t1 : ▹ itree E R) (t2 : ▹ itree E S) -> ▸ (λ x ->  p , (t1 x) ≅ (t2 x))
  --     EqVis1 : ∀ {A B : _} -> {q : A ≡ B} -> (e : E A) -> (t : E B) -> PathP (λ i -> E (q i)) e t -- -> ∀ y -> Σ B (λ z -> ▸ (λ x ->  p , k1 y x ≅ k2 z x))
  --     EqVis2 : ∀ {A B : _} -> {q : A ≡ B} -> (k1 : A -> ▹ (itree E R)) -> (k2 : B -> ▹ (itree E S)) -> ∀ (x : A) -> ▸ (λ t → p , k1 x t ≅ k2 (subst (λ x₁ → x₁) q x) t)

  -- open _, _≅_  

  -- -- Equality
  -- data eqitF {E : Type₀ -> Type₁} {R1 R2 : Type₀} {RR : R1 -> R2 -> Set} (b1 b2 : Bool) vlco (sim : itree E R1 -> itree E R2 -> Set₁) : itree E R1 -> itree E R2 -> Set₁ where
  --   EqRet : ∀ r1 r2 -> (REL : RR r1 r2) -> eqitF b1 b2 vlco sim (Ret r1) (Ret r2)
  --   EqTau : ∀ m1 m2 -> (REL : sim m1 m2) -> eqitF b1 b2 vlco sim (Tau (next m1)) (Tau (next m2))
  --   EqVis : ∀ {u} (e : E u) k1 k2 -> (REL : ∀ v → vlco sim (k1 v) (k2 v)) -> eqitF b1 b2 vlco sim (Vis e k1) (Vis e k2)
  --   EqTauL : ∀ t1 ot2 -> (REL : eqitF b1 b2 vlco sim t1 ot2) -> eqitF b1 b2 vlco sim (Tau (next t1)) ot2 -- (CHECK: b1)
  --   EqTauR : ∀ ot1 t2 -> (REL : eqitF b1 b2 vlco sim ot1 t2) -> eqitF b1 b2 vlco sim ot1 (Tau (next t2)) -- (CHECK: b2)

  -- eqit-pre : ∀ {E : Type₀ -> Type₁} {R1 R2 : Type₀} b1 b2 vlco sim -> itree E R1 -> itree E R2 -> Set₁
  -- eqit-pre b1 b2 vlco sim t1 t2 = eqitF b1 b2 vlco sim t1 t2

  -- id : ∀ {A : Set₀} -> A -> A
  -- id x = x

  -- eqit : ∀ {E : Type₀ -> Type₁} {R1 R2 : Type₀} -> (b1 b2 : Bool) -> itree E R1 -> itree E R2 -> Set₁
  -- eqit b1 b2 = (fix λ x → (eqit-pre b1 b2 id)) {!!}

  -- eq-tree = eqit false false

  -- Equality
  data _≅_ {E} {R} : itree E R -> itree E R -> Set₁ where
    EqRet : (a b : R) -> a ≡ b -> Ret a ≅ Ret b
    EqTau : (t1 : ▹ itree E R) (t2 : ▹ itree E R) -> ▸ (λ x ->  (t1 x) ≅ (t2 x)) -> Tau t1 ≅ Tau t2
    EqVis : ∀ {A B} -> (u : A ≡ B) -> (e : E A) (t : E B) (w : PathP (λ i -> E (u i)) e t) -> (k1 : A -> ▹ (itree E R)) -> (k2 : B -> ▹ (itree E R)) -> PathP (λ i -> u i → ▹ itree E R) k1 k2 -> Vis e k1 ≅ Vis t k2

  mutual
    bisim : ∀ {E R} -> {r s : itree E R} -> r ≅ s -> r ≡ s
    bisim (EqRet t1 t2 q) i = Ret (q i)
    bisim (EqTau t1 t2 q) i = Tau λ x → bisim (q x) i
    bisim {E = E} {R = R}  (EqVis u e t w k1 k2 q) i = Vis (w i) λ x x₁ → q i x x₁

    todo0 : ∀ {E} {R} {rr ss : R} -> Ret {E = E} rr ≡ Ret ss -> rr ≡ ss
    todo0 = {!!}

    todo2 : ∀ {E} {R} {t1 t2 : ▹ itree E R} -> Tau t1 ≡ Tau t2 -> t1 ≡ t2
    todo2 = {!!}

    todo3 : ∀ {E} {R} {A B} {e : E A} {t : E B} {f : A -> ▹ itree E R} {g : B -> ▹ itree E R} -> Vis e f ≡ Vis t g -> A ≡ B
    todo3 = {!!}

    todo4 : ∀ {E} {R} {A B} {e : E A} {t : E B} {f : A -> ▹ itree E R} {g : B -> ▹ itree E R} -> (p : Vis e f ≡ Vis t g) -> PathP (λ i → E (todo3 p i)) e t
    todo4 = {!!}

    todo5 : ∀ {E} {R} {A B} {e : E A} {t : E B} {f : A -> ▹ itree E R} {g : B -> ▹ itree E R} -> (p : Vis e f ≡ Vis t g) -> PathP (λ i → todo3 p i → ▹ itree E R) f g
    todo5 = {!!}


    misib : ∀ {E R} -> {r s : itree E R} -> r ≡ s -> r ≅ s
    misib {r = Ret rr} {s = Ret ss} p = EqRet rr ss (todo0 p)
    misib {r = Tau t1} {s = Tau t2} p = EqTau t1 t2 λ x → misib (λ i -> todo2 p i x)
    misib {r = Vis {A = A} e f} {s = Vis {A = B} t g} p = EqVis (todo3 p) e t (todo4 p) f g {!!}
    misib _ = {!!}  

  -- iso1 : {A : Type₀} → {x y : stream A} → (p : x ≡ y) → bisim (misib p) ≡ p
  -- head  (iso1 p i j)       = stream-hd (p j)
  -- tails (iso1 p i j) tt tt = iso1 (λ i → stream-tl (p i)) i j

  -- iso2 : ∀ {E R} → {x y : itree E R} → (p : x ≅ y) → misib (bisim p) ≡ p
  -- iso2 (EqRet r s p) = λ i → {!!}
  -- iso2 (EqVis e k1 k2 p) = {!!}
  -- iso2 (EqTau t1 t2 p) = {!!}

  -- path≃bisim : ∀ {E R} → {x y : itree E R} → (x ≡ y) ≃ (refl , x ≅ y)
  -- path≃bisim = isoToEquiv (iso misib bisim iso2 iso1)

  -- path≡bisim : {A : Type₀} → {x y : stream A} → (x ≡ y) ≡ (x ≈ y)
  -- path≡bisim = ua path≃bisim

  -- itree-≅-tau : ∀ {E R} (t1 t2 : ▹ itree E R) -> t1 ≡ t2 -> Tau t1 ≡ Tau t2
  -- itree-≅-tau t1 t2 p = λ i -> funExt⁻ {f = Tau} {g = Tau} refl (p i) i

  -- -- TODO'S:
  -- postulate
  --   sim_convert : ∀ {E A B} {R : Set₀} -> ▹ (itree E A -> itree E B -> Set₁) -> (R -> ▹ itree E A) -> (R -> ▹ itree E B) -> Set₁
  --   -- sim_convert = ∀ (v : R) -> sim ⊛ (k1 v) ⊛ (k2 v)
  --   -- sim_convert = (transp k1) ≡ k2

  --   k1k2 : ∀ {E A} {R : Set₀} -> (f : R -> ▹ itree E A) -> (sim : ▹ (itree E A → itree E A → Set₁)) -> sim_convert sim f f

  -- Equality
  -- data euttF {E} {A B : Set₀} {r : A -> B -> Set₀} (sim : ▹ (itree E A -> itree E B -> Set₁)) : (itree E A -> itree E B -> Set₁) where
  --   EqRet : (a : A) -> (b : B) -> (REL : r a b) -> euttF sim (Ret a) (Ret b)
  --   EqVis : {R : Set₀} -> (e : E R) -> (k1 : R -> ▹ (itree E A)) -> (k2 : R -> ▹ (itree E B)) -> (REL : sim_convert sim k1 k2) -> euttF sim (Vis e k1) (Vis e k2)
  --   EqTau : (t1 : itree E A) -> (t2 : itree E B) -> euttF sim (Tau (next t1)) (Tau (next t2)) -- -> (REL : sim t1 t2)
  --   EqTauL : (t1 : itree E A) -> (ot2 : itree E B) -> (REL : euttF {r = r} sim t1 ot2) -> euttF sim (Tau (next t1)) ot2
  --   EqTauR : (ot1 : itree E A) -> (t2 : itree E B) -> (REL : euttF {r = r} sim ot1 t2) -> euttF sim ot1 (Tau (next t2))
  
  -- k1k2m : ∀ {E A B} {R : Set₀} -> (k1 : R -> ▹ itree E A) (k2 : R -> ▹ itree E B) -> (p : A ≡ B) -> PathP (λ x → R → ▹ itree E (p x)) k1 k2
  -- k1k2m = λ k1 k2 p x x₁ x₂ → {!!}

  -- eutt : ∀ {E R S} (rel : R -> S -> Set₀) -> itree E R -> itree E S -> Set₁
  -- eutt rel = fix (euttF {r = rel})

  -- _≈_ : ∀ {E} {R}  -> itree E R -> itree E R -> Set₁
  -- _≈_ {R = R} = eutt _≡_

  -- _≈'_ : ∀ {E : Set₀ -> Set₁} {R : Set₀}  -> (itree E R -> itree E R -> Set₁)
  -- _≈'_ {E = E} {R = R} = euttF {r = _≡_} (next _≈_)

  -- fix-unfold : ∀ {E R S} (rel : R -> S -> Set₀) -> eutt {E} {R} {S} rel ≡ euttF {E} {R} {S} {r = rel} (next (eutt rel))
  -- fix-unfold rel = fix-eq euttF

  -- ≈unfold : ∀ {E R} -> _≈_ {E = E} {R = R} ≡ _≈'_
  -- ≈unfold = fix-eq euttF

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

  -- asdf : ∀ {E} {R} {t1 t2 : itree E R} {k1 k2 : R -> itree E R} -> t1 ≅ t2 -> (∀ x -> k1 x ≅ k2 x) -> bind t1 k1 ≅ bind t2 k2
  -- asdf p q = {!!}

  -- -- Examples
  -- data IO : Type₀ → Type₁ where
  --   Input : IO ℕ
  --   Output : (x : ℕ) -> IO Unit

  -- -- Spin definition
  -- spin-pre : ▹ itree IO ⊥ -> itree IO ⊥
  -- spin-pre spin = Tau spin

  -- spin : itree IO ⊥
  -- spin = fix spin-pre

  -- spin-unroll : spin ≡ spin-pre (next spin)
  -- spin-unroll = fix-eq spin-pre

  -- -- Echo definition
  -- echo-pre : ▹ itree IO ⊥ -> itree IO ⊥
  -- echo-pre echo = Vis Input λ x -> next (Vis (Output x) λ _ → next (Tau echo))

  -- echo : itree IO ⊥
  -- echo = fix echo-pre

  -- echo-unroll : echo ≡ echo-pre (next echo)
  -- echo-unroll = fix-eq echo-pre

  -- -- Echo definition trigger
  -- echo2-pre : ▹ itree IO ⊥ -> itree IO ⊥
  -- echo2-pre echo2 = bind (trigger Input) λ x -> bind (trigger (Output x)) λ _ → Tau echo2

  -- echo2 : itree IO ⊥
  -- echo2 = fix echo2-pre

  -- -- forever
  -- forever : ∀ {E R S} -> (t : itree E R) -> itree E S
  -- forever t = fix λ x → bind t λ _ → Tau x

  -- echo3 : itree IO ⊥
  -- echo3 = forever (Vis Input λ x -> next (Vis (Output x) λ u → next (Ret u)))
