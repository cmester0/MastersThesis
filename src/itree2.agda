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

RetD : ∀ {R} -> R -> Delay-IT R
RetD r = now r

RetD' : ∀ {R} -> R -> Delay R
ValueD (RetD' r) = now r

P1 : ∀ {R} (f : Delay R -> Delay R) -> Delay-IT R -> Delay-IT R
P1 = λ f x → ValueD (f (record { ValueD = x }))

record qpf {R} (F₀ : Set -> Set) (F₁ : ∀ (f : (Delay R) -> (Delay R)) -> F₀ (Delay R) -> F₀ (Delay R)) : Set₁ where
  field
    abs : Delay-IT R -> F₀ (Delay R)
    repr : F₀ (Delay R) -> Delay-IT R
    abs_repr : (x : F₀ (Delay R)) -> (abs ∘ repr) x ≡ x
    abs_map : ∀ (f : Delay R -> Delay R) -> abs ∘ (P1 f) ≡ (F₁ f) ∘ abs

open qpf

spin' : ∀ {R} -> Delay R
ValueD spin' = later spin'

spin : ∀ {R} -> Delay-IT R
spin = ValueD spin'

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

as : ∀ {E} {R} {x} -> (ValueIT {E} {R} (record { ValueIT = x }) ≡ x)
as = refl

mutual
  bisim-ITree-pre : ∀ {E R} (x y : ITree-IT E R) -> ITreeBisim-pre x y -> x ≡ y
  bisim-ITree-pre x y (EqRet p) i = rret (p i)
  bisim-ITree-pre x y (EqTau {t} {u} p) i = ttau (bisim-ITree t u p i)
  bisim-ITree-pre x y (EqVis {e = e} p) i = vvis (_ , e , (p i))
  
  bisim-ITree : ∀ {E R} (x y : ITree E R) -> ITreeBisim x y -> x ≡ y
  bisim-ITree x y (Eq p) i = {!!}

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

-- Echo' : ITree IO ⊥
-- ValueIT Echo' = Bind' (Trigger Input) λ x → Bind' (Trigger (Output x)) λ _ → Tau Echo'

-- Echo : ITree IO ⊥ -> ITree IO ⊥
-- ValueIT (Echo e) = vvis ( _ , Input , λ x → Bind (ValueIT (record { ValueIT = rret x })) (λ x → vvis (_ , Output x , λ x → Bind (ValueIT record { ValueIT = rret x }) (λ _ → ttau (record { ValueIT = ValueIT e})))))

Echo : ITree IO ⊥ -> ITree IO ⊥
-- Echo e = record { ValueIT = vvis ( _ , Input , λ x → Bind (rret x ) (λ x → vvis (_ , Output x , λ x → Bind (rret x) (λ _ → ttau (record { ValueIT = ValueIT e}))))) }
Echo e = record { ValueIT = vvis ( _ , Input , λ x → record { ValueIT = vvis (_ , Output x , λ _ → record { ValueIT = ttau (record { ValueIT = ValueIT e}) }) }) }

Echo' : ITree IO ⊥ -> ITree IO ⊥
Echo' e = record { ValueIT = Bind' (Trigger Input) λ x → Bind' (Trigger (Output x)) λ _ → Tau (ValueIT e) }

Echo2 : ITree IO ⊥ -> ITree IO ⊥
Echo2 e = record { ValueIT = vvis (_ , Input , λ x → record { ValueIT = vvis (_ , Output x , λ _ → record { ValueIT = ttau (record { ValueIT = ValueIT e })} )} )}

-- ttau (record { ValueIT = ValueIT e })

-- vvis (A , (e , (λ x → record { ValueIT = k x })))

-- ASD : ∀ {E R S} (k : R -> ITree-IT E S) -> k ≡ λ x -> Bind (rret x ) k
-- ASD = {!!}

asddf : ∀ {E} {R S : Set} (k : R -> ITree-IT E S) (x : R) -> Bind (rret x ) k ≡ record { ValueIT = k x }
asddf = λ k x → {!!}

BindEquality : ∀ {E R S} e k -> Bind' {E = E} {R = R} {S = S} (Trigger e) k ≡ vvis (R , e , λ x -> Bind (rret x ) k)
BindEquality = λ e k -> refl

Echo-Bind-Equiv : Echo ≡ Echo2
Echo-Bind-Equiv = λ i x → bisim-ITree (Echo x) (Echo2 x) (Eq (EqVis λ i₁ x₁ → record { ValueIT = vvis (Unit , (Output x₁ , λ x₂ → record { ValueIT = ttau (record { ValueIT = ValueIT x }) })) })) i

Echo-Bind-Equiv' : Echo' ≡ Echo2
Echo-Bind-Equiv' = λ i e → record { ValueIT = vvis (ℕ , Input , λ x → {!!}) }

-- data ITreeBisim {E : Set -> Set₁} {R : Set} : (_ _ : ITree E R) -> Set₁ where
--   EqRet : ∀ (r s : R) -> r ≡ s -> ITreeBisim {E} (Ret' r) (Ret' s)
--   EqTau : ∀ t u -> ITreeBisim t u -> ITreeBisim {E} {R} (Tau'' t) (Tau'' u)
--   EqVis : ∀ {A} e k1 k2 -> k1 ≡ k2 -> ITreeBisim (Vis'' {A = A} e k1) (Vis'' {A = A} e k2)

-- Echo : ITree IO ⊥
-- ValueIT Echo = Bind' (Trigger Input) λ x → Bind' (Trigger (Output x)) λ _ → Tau' Echo

-- Echo2 : ITree IO ⊥
-- ValueIT Echo2 = Vis (Input) λ x → Vis (Output x) λ _ → Tau' Echo2
