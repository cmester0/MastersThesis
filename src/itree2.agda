{-# OPTIONS --cubical --guardedness  #-} --safe

module itree2 where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients

-- Delay
mutual
  data Delay-IT (R : Set) : Set where
    later : Delay R -> Delay-IT R
    now : R -> Delay-IT R

  record Delay (R : Set₀) : Set where
    coinductive
    field
      ValueD : Delay-IT R

open Delay

TauD : ∀ {R} -> Delay-IT R -> Delay-IT R
TauD t = t

TauD' : ∀ {R} -> Delay R -> Delay-IT R
TauD' t = later t

TauD'' : ∀ {R} -> Delay R -> Delay R
ValueD (TauD'' t) = TauD' t

RetD : ∀ {R} -> R -> Delay-IT R
RetD r = now r

RetD' : ∀ {R} -> R -> Delay R
ValueD (RetD' r) = now r

spin' : ∀ {R} -> Delay R
ValueD spin' = later spin'

-- Delay weak bisimulation

mutual
  record ∞delay≈ {R} (x : Delay R) (y : Delay R) : Set where
    coinductive
    field
      force : delay≈ (ValueD x) (ValueD y)

  data delay≈ {R} : (Delay-IT R) -> (Delay-IT R) -> Set where
    EqNow : ∀ {r s : R} -> r ≡ s -> delay≈ (now r) (now s)
    EqLater : ∀ {t u} -> (∞delay≈ t u) -> delay≈ (later t) (later u)

open ∞delay≈

mutual
  ∞delay≈-refl : ∀ {R} {x : Delay R} -> ∞delay≈ x x
  force ∞delay≈-refl = delay≈-refl

  delay≈-refl : ∀ {R} {x : Delay-IT R} -> delay≈ x x
  delay≈-refl {x = now r} = EqNow refl
  delay≈-refl {x = later t} = EqLater ∞delay≈-refl

mutual
  ∞delay-bisim : ∀ R a b -> ∞delay≈ {R} a b -> a ≡ b
  ValueD (∞delay-bisim R a b p i) = delay-bisim R (ValueD a) (ValueD b) (force p) i

  delay-bisim : ∀ R a b -> delay≈ {R} a b -> a ≡ b
  delay-bisim R (now r) (now s) (EqNow p) = λ i → now (p i)
  delay-bisim R (later t) (later u) (EqLater p) = λ i → later (∞delay-bisim R t u p i)

mutual
  data weak-delay≈ {R} : (Delay-IT R) -> (Delay-IT R) -> Set where
    EqNow : ∀ {r s : R} -> r ≡ s -> weak-delay≈ (now r) (now s)
    EqLater : ∀ {t u} -> (∞weak-delay≈ t u) -> weak-delay≈ (later t) (later u)
    EqLaterL : ∀ {t u} -> (∞weak-delay≈ t record { ValueD = u }) -> weak-delay≈ (later t) u
    EqLaterR : ∀ {t u} -> (∞weak-delay≈ record { ValueD = t} u) -> weak-delay≈ t (later u)

  record ∞weak-delay≈ {R} (x : Delay R) (y : Delay R) : Set where
    coinductive
    field
      force : weak-delay≈ (ValueD x) (ValueD y)

open ∞weak-delay≈

mutual
  ∞weak-delay≈-refl : ∀ {R} {x : Delay R} -> ∞weak-delay≈ x x
  force ∞weak-delay≈-refl = weak-delay≈-refl

  weak-delay≈-refl : ∀ {R} {x : Delay-IT R} -> weak-delay≈ x x
  weak-delay≈-refl {x = now r} = EqNow refl
  weak-delay≈-refl {x = later t} = EqLater ∞weak-delay≈-refl

-- weak
mutual
  ∞weak-delay-bisim : ∀ R a b -> ∞weak-delay≈ {R} a b -> a ≡ b
  ValueD (∞weak-delay-bisim R a b p i) = weak-delay-bisim R (ValueD a) (ValueD b) (force p) i

  postulate
    helper0 : ∀ {R} t s p -> later t ≡ ValueD (∞weak-delay-bisim R t (record { ValueD = now s }) p i0)
    helper1 : ∀ {R} r u p -> ValueD (∞weak-delay-bisim R (record { ValueD = now r }) u p i1) ≡ later u

  weak-delay-bisim : ∀ R a b -> weak-delay≈ {R} a b -> a ≡ b
  weak-delay-bisim R (now r) (now s) (EqNow p) = λ i → now (p i)
  weak-delay-bisim R (later t) (now s) (EqLaterL p) = λ i → compPath-filler (helper0 t s p) (λ i -> ValueD (∞weak-delay-bisim R t (record { ValueD = now s }) p i)) i i
  weak-delay-bisim R (now r) (later u) (EqLaterR p) = λ i → compPath-filler (λ i -> ValueD (∞weak-delay-bisim R (record { ValueD = now r }) u p i)) (helper1 r u p) i i
  weak-delay-bisim R (later t) (later u) (EqLater p) = λ i → later (∞weak-delay-bisim R t u p i)

-- Quotiented delay

quotient-delay : ∀ {R} -> Delay-IT R -> Delay-IT R / (weak-delay≈ {R})
quotient-delay (later t) = eq/ (later t) (ValueD t) (EqLaterL (record { force = weak-delay≈-refl })) i0
quotient-delay (now r) = [ now r ]

-- weak-delay is equality

-- ∀ t u -> ValueD t ≡ ValueD u -> u ≡ u

tau-equiv : ∀ {R} (t : Delay R) -> later t ≡ ValueD t
tau-equiv = {!!}

-- delay-bisim R (later t) (later u) (EqLater p) = λ i → later ?

-- delay examples

spin : ∀ {R} -> Delay-IT R
spin = ValueD spin'

spin-is-delay-spin : ∀ {R} -> TauD {R} spin ≡ spin
spin-is-delay-spin = {!!}

-- Tree
record Tree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueT : Σ Set (λ A -> E A × (A -> Tree E R)) ⊎ R

open Tree

TreeIT : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁ -- tree inner type
TreeIT E R = Σ Set (λ A -> E A × (A -> Tree E R)) ⊎ R

TreeRet : ∀ {E} {R} -> R -> Tree E R
ValueT (TreeRet r) = inr r

TreeVis : ∀ {E} {R} -> ∀ {A} -> E A -> (A -> TreeIT E R) -> TreeIT E R
TreeVis {A = A} e k = inl (A , e , λ x -> record { ValueT = k x } )

-- ITree
mutual
  record ITree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
    coinductive
    field
      ValueIT : ITree-IT E R

  data ITree-IT (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
    ttau : ITree E R -> ITree-IT E R
    vvis : Σ Set (λ A -> E A × (A -> ITree E R)) -> ITree-IT E R
    rret : R -> ITree-IT E R

open ITree

Ret : {E : Set -> Set₁} {R : Set} -> R -> ITree-IT E R
Ret = rret

Tau : {E : Set -> Set₁} {R : Set} -> ITree-IT E R -> ITree-IT E R
Tau t = ttau (record { ValueIT = t })

Vis : {E : Set -> Set₁} {R : Set} -> ∀ {A} -> E A -> (A -> ITree-IT E R)  -> ITree-IT E R
Vis {A = A} e k = vvis (A , (e , (λ x → record { ValueIT = k x })))

mutual
  data ITreeBisim-pre {E : Set -> Set₁} {R : Set} : (_ _ : ITree-IT E R) -> Set₁ where
    EqRet : ∀ {r s : R} -> r ≡ s -> ITreeBisim-pre {E} (rret r) (rret s)
    EqTau : ∀ {t u} -> ITreeBisim t u -> ITreeBisim-pre {E} {R} (ttau t) (ttau u)
    EqVis : ∀ {A} {e k1 k2} -> k1 ≡ k2 -> ITreeBisim-pre (vvis (A , e , k1)) (vvis (A , e , k2))

  data ITreeBisim {E : Set -> Set₁} {R : Set} : (_ _ : ITree E R) -> Set₁ where
    Eq : ∀ {x y} -> ITreeBisim-pre (ValueIT x) (ValueIT y) -> ITreeBisim x y

Bind : ∀ {E R S} -> ITree-IT E R -> (R -> ITree-IT E S) -> ITree E S
ValueIT (Bind (rret r) k) = k r
-- Bind (rret r) k = record { ValueIT = k r }
ValueIT (Bind (ttau t) k) = ttau (Bind (ValueIT t) k)
ValueIT (Bind (vvis (A , e , k)) k') = vvis ( _ , e , λ x → Bind (ValueIT (k x)) k' )

Bind' : ∀ {E R S} -> ITree-IT E R -> (R -> ITree-IT E S) -> ITree-IT E S
Bind' r k = ValueIT (Bind r k)

Bind'' : ∀ {E R S} -> ITree E R -> (R -> ITree E S) -> ITree E S
Bind'' r k = Bind (ValueIT r) (λ x -> ValueIT (k x))

Bind2 = Bind'

syntax Bind' e₁ (λ x → e₂) = x ← e₁ , e₂
syntax Bind2 e₁ (λ _ → e₂) = e₁ ,, e₂
infixr 2 Bind
infixr 3 Bind2

Trigger : ∀ {E} {R} -> (e : E R) -> ITree-IT E R
Trigger e = Vis e Ret

Trigger' : ∀ {E} {R} -> (e : E R) -> ITree E R
ValueIT (Trigger' e) = Vis e Ret

-- Data types used in examples
data IO : Type₀ → Type₁ where
  Input : IO ℕ
  Output : (x : ℕ) -> IO Unit

Echo : ITree IO ⊥ -> ITree IO ⊥
-- Echo e = record { ValueIT = vvis ( _ , Input , λ x → Bind (rret x ) (λ x → vvis (_ , Output x , λ x → Bind (rret x) (λ _ → ttau (record { ValueIT = ValueIT e}))))) }
Echo e = record { ValueIT = vvis ( _ , Input , λ x → record { ValueIT = vvis (_ , Output x , λ _ → record { ValueIT = ttau (record { ValueIT = ValueIT e}) }) }) }

Echo' : ITree IO ⊥ -> ITree IO ⊥
Echo' e = record { ValueIT = Bind' (Trigger Input) λ x → Bind' (Trigger (Output x)) λ _ → Tau (ValueIT e) }

Echo2 : ITree IO ⊥ -> ITree IO ⊥
Echo2 e = record { ValueIT = vvis (_ , Input , λ x → record { ValueIT = vvis (_ , Output x , λ _ → record { ValueIT = ttau (record { ValueIT = ValueIT e })} )} )}

BindEquality : ∀ {E R S} e k -> Bind' {E = E} {R = R} {S = S} (Trigger e) k ≡ vvis (R , e , λ x -> Bind (rret x ) k)
BindEquality = λ e k -> refl
