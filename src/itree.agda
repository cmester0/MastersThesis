{-# OPTIONS --cubical --guardedness --safe --copatterns #-}  

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Codata.M

open import Agda.Builtin.Coinduction

-- open import Cubical.HITs.SetQuotients -- _/_
-- open import Cubical.Foundations.Univalence -- ua

-- open import Later
open import Cubical.Data.Prod

module itree where
  record monad (M : Type₀ -> Type₀) : Type₁ where
    coinductive
    field 
      ret : {A : Type₀} -> A -> M A
      bind : {A B : Type₀} -> M A -> (A -> M B) -> M B

  record Functor {n m} {ℂ : Type n} {𝔻 : Type m}  : Type (ℓ-suc (ℓ-max n m)) where
    inductive
    field
      F₀ : ℂ → 𝔻
      F₁ : (ℂ → ℂ) → (𝔻 → 𝔻)

  -- ▹_ : ∀ {ℓ} {ℂ : Type ℓ} -> Functor {n = ℓ-suc ℓ} {m = ℓ-suc ℓ} {ℂ = ℂ × ℕ → Type ℓ} {𝔻 = ℂ × ℕ -> Type ℓ}
  -- Functor.F₀ ▹_ X (x , 0) = Lift Unit
  -- Functor.F₀ ▹_ X (x , (ℕ.suc m)) = X (x , m)
  -- Functor.F₁ ▹_ X = {!!}

  id : ∀ {ℓ} {ℂ : Type ℓ} -> Functor {ℂ = ℂ} {𝔻 = ℂ}
  Functor.F₀ id x = x
  Functor.F₁ id f = f

  -- next : ∀ {ℓ} {ℂ : Type ℓ} -> id {ℓ = ℓ-suc ℓ} {ℂ = ℂ × ℕ → Type ℓ} -> ▹_ {ℂ = ℂ}
  -- next X x 0 = Unit
  -- next X x (ℕ.suc n) = X (id {ℂ = x} , ℕ.suc)

  -- next2 : Functor.F₀ ▹_ (λ x -> x ≡ (2 , 2)) ≡ Lift Unit
  -- next2 = refl

  -- X : (ℂ × ℕ → Set) -> ℂ × ℕ → Set
  -- X : (ℂ × ℕ → Set) -> ℂ × ℕ → Set

  -- ▹₁_ : ∀ {ℂ : Type _} -> (X : (ℂ × ℕ -> ℂ × ℕ) -> Set) -> (ℂ × ℕ -> ℂ × ℕ) -> ℂ × ℕ -> Set
  -- ▹₁_ = {!!}

  
  -- data itree {ℓ : Level} (Event : Type ℓ -> Type (ℓ-suc ℓ)) (Result : Type ℓ) : Type (ℓ-suc ℓ) where
  --   Ret : Result -> itree Event Result
  --   Tau : ∞ (itree {ℓ = ℓ} Event Result) -> itree {ℓ = ℓ} Event Result
  --   Vis : {Answer : Type ℓ} -> Event Answer -> (Answer -> ∞ (itree {ℓ = ℓ} Event Result)) -> itree {ℓ = ℓ} Event Result

  mutual
    data itree {ℓ : Level} (Event : Type ℓ -> Type (ℓ-suc ℓ)) (Result : Type ℓ) : Type (ℓ-suc ℓ) where
      Ret : Result -> itree Event Result
      Tau : itree Event Result -> itree Event Result
      Vis : {Answer : Type ℓ} -> Event Answer -> (Answer -> itree Event Result) -> itree {ℓ = ℓ} Event Result
      
    -- record asdf {ℓ : Level} (Event : Type ℓ -> Type (ℓ-suc ℓ)) (Result : Type ℓ) : Type (ℓ-suc (ℓ-suc ℓ)) where
    --   field
    --     exit : itree Event Result
    --     Tau : itree Event Result ≡ itree Event Result

  -- asdfasd : ∀ x -> Tau x ≡ x
  -- asdfasd (Ret a) = λ i → {!!}
  
  data bot {ℓ} : Type ℓ where
  
  -- Examples
  data IO : Type₀ → Type₁ where
    Input : IO ℕ
    Output : (x : ℕ) -> IO Unit

  -- mutual
  --   spin : itree IO ⊥
  --   spin = Tau spin

  -- echo : asdf IO ⊥
  -- asdf.exit echo = Vis Input λ x -> Vis (Output x) λ _ → {!!}
  -- asdf.Tau echo = λ i -> transp {!!} {!!} {!!}

  -- mutual    
  --   echo : itree IO ⊥
  --   echo = Vis Input λ x -> Vis (Output x) λ _ → Tau echo

  -- -- The following seems wrong
  mutual
    bind : ∀ {ℓ} {E} {A} {B} -> itree {ℓ = ℓ} E A -> (A -> itree E B) -> itree E B
    bind (Ret r) k = k r
    bind (Tau t) k = Tau (bind t k)
    bind (Vis e f) k = Vis e (λ x -> bind (f x) k)

-- now (Vis e (λ x -> bind (▹itree.step (f x)) k))
    -- bind (Vis e f) k = now (Vis e (λ x -> bind (▹itree.step (f x)) k))
    
    -- bind : ∀ {ℓ} {E} {A} {B} -> itree {ℓ = ℓ} E A -> (A -> ▹itree E B) -> itree E B
    -- bind t k = bind₀ t k

  -- _#_ = bind

  -- _#'_ : ∀ {ℓ} {E} {A} {B} -> itree {ℓ = ℓ} E A -> itree E B -> itree E B
  -- _#'_ a b = bind a (λ _ -> ♯ b)
  
  -- ret : ∀ {ℓ} {Event} {Result} -> Result -> itree {ℓ = ℓ} Event Result
  -- ret = Ret

  -- trigger : ∀ {ℓ} {E : Type ℓ -> Type (ℓ-suc ℓ)} {A : Type ℓ} -> E A -> itree {ℓ = ℓ} E A
  -- trigger e = Vis e (λ x -> ♯ Ret x)

  -- echo2 : itree IO void
  -- echo2 = trigger Input # λ x -> (♯ (trigger (Output x) #' echo2))

  -- Equality
  -- {r : A → B → Type₁}
  -- data euttF {E} {A B} {r : A -> B -> Set₀} (sim : ∞ (itree E A -> itree E B -> Set₁)) : (itree E A -> itree E B -> Set₁) where -- 
  --   EqRet : (a : A) -> (b : B) -> (REL : r a b) -> euttF sim (Ret a) (Ret b) -- (REL : r a b)
  --   EqVis : {R : _} -> (e : E R) -> (k1 : R -> ∞ (itree E A)) -> (k2 : R -> ∞ (itree E B)) -> (REL : ∀ (v : R) -> (♭ sim) (♭ (k1 v)) (♭ (k2 v))) -> euttF sim (Vis e k1) (Vis e k2)
  --   EqTau : (t1 : itree E A) -> (t2 : itree E B) -> (REL : (♭ sim) t1 t2) -> euttF sim (Tau (♯ t1)) (Tau (♯ t2))
  --   EqTauL : (t1 : itree E A) -> (ot2 : itree E B) -> (REL : euttF {r = r} sim t1 ot2) -> euttF sim (Tau (♯ t1)) ot2
  --   EqTauR : (ot1 : itree E A) -> (t2 : itree E B) -> (REL : euttF {r = r} sim ot1 t2) -> euttF sim ot1 (Tau (♯ t2))

  -- euttf-monotone : ∀ {E} {A B} {r} (sim sim' : ∞ (itree E A -> itree E B -> Type₁)) -> (LE : sim ≡ sim') -> (euttF sim ≡ euttF sim')
  -- euttF-Monotone {r = r} sim sim' LE = λ i -> euttF {r = r} (LE i)    

  -- euttF_fix_help : ∀ {E} {A B} {r} (sim : ∞ (itree E A -> itree E B -> Set₁)) -> sim ≡ ♯ euttF {r = r} sim
  -- euttF_fix_help {E} {A} {B} {r} sim = λ i → {!!}
  
  -- euttF_fix_help : ∀ {E} {A B} {r} sim -> euttF {E = E} {A = A} {B = B} {r = r} sim ≡ euttF {E = E} {A = A} {B = B} {r = r} (♯ euttF {E = E} {A = A} {B = B} {r = r} sim)
  -- euttF_fix_help {E} {A} {B} {r} sim = euttF-Monotone sim (♯ euttF {E = E} {A = A} {B = B} {r = r} sim) {!!}
  
  -- eutt : ∀ {E} {A B} {r} -> itree E A -> itree E B -> Type₁
  -- eutt {r = r} = euttF {r = r} (♯ eutt {r = r})

  postulate
    ≡Tau : ∀ {ℓ E A} (t : itree {ℓ = ℓ} E A) -> Tau t ≡ t

  _≈_ : {ℓ : Level} {Event : Type ℓ -> Type (ℓ-suc ℓ)} {Result : Type ℓ} -> itree Event Result -> itree Event Result -> Type (ℓ-suc ℓ)
  _≈_ {ℓ} {Event} (Ret a) (Ret b) = a ≡ b -> (Ret {Event = Event} a) ≡ (Ret b) -- EqRet
  _≈_ {ℓ} {Event} {Result} (Tau a) (Tau b) = a ≡ b
  _≈_ {ℓ} {Event} {Result} (Vis {A} a f) (Vis {B} b g) = (p : A ≡ B) -> PathP (λ i -> Event (p i)) a b -> PathP (λ i -> p i -> itree Event Result) f g -> Path (itree Event Result) (Vis a f) (Vis b g) -- EqVis
  _≈_ {ℓ} {Event} {Result} (Tau a) b = (∀ (x : itree Event Result) -> Path (itree Event Result) (Tau x) x) -> Path (itree Event Result) a b -> Path (itree Event Result) (Tau a) b -- EqTauR
  _≈_ {ℓ} {Event} {Result} a (Tau b) = Path (itree Event Result) a b -> Path (itree Event Result) a (Tau b) -- EqTauL
  _≈_ (Ret a) (Vis b g) = bot
  _≈_ (Vis a f) (Ret b) = bot

  postulate
    ≈Tau : ∀ {ℓ E A} (t : itree {ℓ = ℓ} E A) -> Tau t ≈ t
    ≈Tau-bind : ∀ {ℓ E A B} t (k : A -> itree {ℓ = ℓ} E B) ->
                  bind (Tau t) k ≈ Tau (bind t k)
    ≈Vis-bind : ∀ {ℓ E A B} (e : E A) (k1 : A -> itree {ℓ = ℓ} E B) (k2 : _ -> itree {ℓ = ℓ} E B) -> bind (Vis e k1) k2 ≈ Vis e (λ y -> bind (k1 y) k2)

  asdf : ∀ {ℓ E A} (t : itree {ℓ = ℓ} E A) -> bind t (λ x -> Ret x) ≡ t
  asdf (Ret a) = λ i → Ret a
  asdf (Tau t) = λ i → {!!}
  asdf (Vis a f) = λ i → Vis {!!} {!!}

  -- ≈Tau2 : ∀ {ℓ E A} (t1 t2 : itree {ℓ = ℓ} E A) -> t1 ≈ t2 -> Tau t1 ≈ Tau t2
  -- ≈Tau2 t1 t2 p = λ i → {!!}

  -- ≈Ret : ∀ A B -> (t1 : A) (t2 : B) -> A ≡ B -> t1 ≡ t2 -> Ret t1 ≡ Ret t2
  -- ≈Ret t1 t2 = λ i -> ?

  -- _≈_ : {ℓ : Level} {Event : Type ℓ -> Type (ℓ-suc ℓ)} {Result : Type ℓ} -> itree Event Result -> itree Event Result -> Type (ℓ-suc ℓ)
  -- _≈_ {ℓ} {Event} {Result} (Ret a) (Ret b) = Path Result a b -> Path (itree Event Result) (Ret a) (Ret b) -- EqRet
  -- _≈_ {ℓ} {Event} {Result} (Tau a) (Tau b) = Path (itree Event Result) (♭ a) (♭ b)
  -- _≈_ {ℓ} {Event} {Result} (Vis {A} a f) (Vis {B} b g) = (p : Path (Type ℓ) A B) -> PathP (λ i -> Event (p i)) a b -> PathP (λ i -> p i -> ∞ (itree Event Result)) f g -> Path (itree Event Result) (Vis a f) (Vis b g) -- EqVis
  -- _≈_ {ℓ} {Event} {Result} (Tau a) b = (∀ (x : itree Event Result) -> Path (itree Event Result) (Tau (♯ x)) x) -> Path (itree Event Result) (♭ a) b -> Path (itree Event Result) (Tau a) b -- EqTauR
  -- _≈_ {ℓ} {Event} {Result} a (Tau b) = Path (itree Event Result) a (♭ b) -> Path (itree Event Result) a (Tau b) -- EqTauL
  -- _≈_ (Ret a) (Vis b g) = bot
  -- _≈_ (Vis a f) (Ret b) = bot  

  

  -- asdf : ∀ {Event} {Result} -> itree Event Result / _≈_
  -- asdf = {!!}

  -- record monad (M : Type₀ -> Type₀) : Type₁ where
  --   coinductive
  --   field 
  --     ret : {A : Type₀} -> A -> M A
  --     bind : {A B : Type₀} -> M A -> (A -> M B) -> M B

  -- data Maybe (A : Type₀) : Type₀ where
  --   nothing : Maybe A
  --   just    : (x : A) → Maybe A
    
  -- option_monad : monad Maybe
  -- monad.ret option_monad = just
  -- monad.bind option_monad (just x) f = f x
  -- monad.bind option_monad nothing _ = nothing
