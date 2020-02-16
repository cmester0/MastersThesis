{-# OPTIONS --cubical --safe --guardedness #-}
module M where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Foundations.Function

open import Cubical.Foundations.Id using (Id)

record Container {ℓ} : Set (ℓ-suc ℓ) where
  constructor _-,-_
  field
    A : Set ℓ
    B : A -> Set ℓ

open Container

P₀ : ∀ {ℓ} -> ∀ {S : Container {ℓ = ℓ}} -> Set ℓ -> Set ℓ
P₀ {S = S} = λ X -> Σ (A S) λ x → (B S x) -> X

P₁ : ∀ {ℓ} {S : Container} {X Y : Set ℓ} -> (f : X -> Y) -> P₀ {S = S} X -> P₀ {S = S} Y
P₁ {S} f = λ { (a , g) -> a , f ∘ g }

Coalg₀ : ∀ {S : Container} -> Set₁
Coalg₀ {S = S} = Σ Set₀ λ C → C → P₀ {S = S} C  

Coalg₁ : ∀ {S : Container} -> Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set₀
Coalg₁ {S = S} (C , γ) (D , δ) = Σ (C → D) λ f → δ ∘ f ≡ (P₁ f) ∘ γ

_⇒_ = Coalg₁

Final : ∀ {S : Container} -> Set₁
Final {S = S} = Σ (Coalg₀ {S = S}) λ X,ρ → ∀ (C,γ : Coalg₀) -> isContr (C,γ ⇒ X,ρ)

record Chain {ℓ} : Set (ℓ-suc ℓ) where
  constructor _,,_
  field
    X : ℕ -> Set ℓ
    π : {n : ℕ} -> X (suc n) -> X n

open Chain

L : ∀ {ℓ} -> Chain {ℓ} → Set ℓ
L (x ,, pi) = Σ ((n : ℕ) → x n) λ x → (n : ℕ) → pi {n = n} (x (suc n)) ≡ x n

Cone : ∀ (A : Set₀) -> ∀ (_ : Chain) -> Set₁
Cone A (X ,, pi) = (A → L (X ,, pi)) ≡ (Σ ((n : ℕ) → A → X n) λ f → (n : ℕ) → pi ∘ f (suc n) ≡ f n)

Z = λ (X : ℕ -> Set) (l : ∀ (n : ℕ) -> X n -> X (suc n)) -> Σ ((n : ℕ) → X n) λ x → (n : ℕ) → x (suc n) ≡ l n (x n)

-- lemma11 : ∀ (X : ℕ -> Set) (l : ∀ (n : ℕ) -> X n -> X (suc n)) -> ∀ (f : Z X l -> X 0) -> isEquiv f
-- lemma11 X l f = {!!}

shift-chain : ∀ {ℓ} -> Chain {ℓ} -> Chain {ℓ}
shift-chain = λ X,π -> ((λ x → X X,π (suc x)) ,, λ {n} → π X,π {suc n})

-- Lemma 12
L-unique : ∀ {ℓ} -> {X,π : Chain {ℓ}} -> L (shift-chain X,π) ≡ L X,π
L-unique = {!!}

! : ∀ {ℓ} {A : Set ℓ} (x : A) -> Lift {ℓ-zero} {ℓ} Unit
! x = lift tt

sequence-pre₀ : ∀ {ℓ} -> Container {ℓ} -> ℕ -> Set ℓ
sequence-pre₀ S 0 = Lift Unit
sequence-pre₀ S (suc n) = P₀ {S = S} (sequence-pre₀ S n)

sequence-pre₁ : ∀ {ℓ} -> (S : Container {ℓ}) -> {n : ℕ} -> sequence-pre₀ S (suc n) -> sequence-pre₀ S n
sequence-pre₁ {ℓ} S {0} = ! {ℓ}
sequence-pre₁ S {suc n} = P₁ (sequence-pre₁ S {n})

sequence : ∀ {ℓ} -> Container {ℓ} -> Chain {ℓ}
X (sequence {ℓ} S) n = sequence-pre₀ {ℓ} S n
π (sequence {ℓ} S) {n} = sequence-pre₁ {ℓ} S

M : ∀ {ℓ} -> Container {ℓ} → Set ℓ
M = L ∘ sequence

Ms : Container → Set
Ms = L ∘ shift-chain ∘ sequence

L,π : ∀ {ℓ} -> Container {ℓ} -> Container
L,π S = (M S -,- λ x -> X (sequence S) 0)

α : ∀ {ℓ} -> {c : Chain {ℓ}} -> L c -> L (shift-chain c)
α = {!!}

PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
PX,Pπ S = (λ z → P₀ {S = S} (X (sequence S) z)) ,, λ x → P₁ (λ z → z) (π (sequence S) x) -- TODO: ID func?

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> M S ≡ P₀ {S = S} (L (PX,Pπ S))
α-iso {S = S} = {!!}

helper : ∀ {ℓ} {S} -> P₀ {ℓ} {S = S} (L (PX,Pπ S)) ≡ P₀ {S = S} (M S)
helper {S = S} = {!!} -- L-unique {sequence S}

shift : ∀ {ℓ} {S : Container {ℓ}} -> M S ≡ P₀ {S = S} (M S)
shift {S = S} = λ i -> compPath-filler {x = M S} {y = P₀ {S = S} (L (PX,Pπ S))} {z = P₀ {S = S} (M S)} α-iso helper i i

in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ {S = S} (M S) -> M S
in-fun {S = S} a = transp (λ i → shift {S = S} (~ i)) i0 a

out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M S -> P₀ {S = S} (M S)
out-fun {S = S} a = transp (λ i → shift {S = S} i) i0 a

-- bisimulation
record bisimulation (S : Container) (R : Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set₀) : Set₁ where
  field
    αᵣ : let R⁻ = Σ (Coalg₀ {S}) (λ a -> Σ (Coalg₀ {S}) (λ b -> R a b)) in R⁻ -> P₀ {S = {!!}} R⁻

coinduction : ∀ (S : Container) -> ∀ (R : Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set₀) -> bisimulation S R -> ∀ m m' -> R m m' -> m ≡ m'
coinduction S R x m m' rel = λ i → {!!}

-- Stream example

stream-S : ∀ A -> Container
stream-S A = (A -,- (λ _ → Unit))

stream : ∀ (A : Set₀) -> Set₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

record Stream A : Set₀ where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

stream-to-Stream : ∀ {A} -> stream A -> Stream A
head (stream-to-Stream s) = hd s
tail (stream-to-Stream s) = stream-to-Stream (tl s)

Stream-to-stream : ∀ {A} -> Stream A -> stream A
Stream-to-stream {A} S = cons (head S) (Stream-to-stream {A} (tail S))

stream-equiv : ∀ {A} -> isEquiv (stream-to-Stream {A})
stream-equiv = {!!}

-- itrees (and buildup examples)

record Delay (R) : Set₀ where
  coinductive
  field
    ValueD : Delay R ⊎ R

open Delay

RetD : ∀ {R : Set₀} -> R -> Delay R
ValueD (RetD r) = inr r

TauD : ∀ {R : Set₀} -> Delay R -> Delay R
ValueD (TauD t) = inl t

delay-S : ∀ (R : Set₀) -> Container
delay-S R = (R -,- λ { _ -> Unit })

delay : ∀ R -> Set₀
delay R = M (delay-S R)

delay-ret-S : ∀ {R : Set₀} -> R -> delay R
delay-ret-S r = {!!}

delay-ret : ∀ {R : Set₀} -> R -> delay R
delay-ret r = in-fun (r , λ x → {!!}) 

delay-tau : ∀ {R} -> delay R -> delay R
delay-tau S = out-fun S .snd {!!}

-- delay examples
spin : ∀ {R} -> Delay R
ValueD spin = inl spin

delay-once : ∀ {R} -> R -> Delay R
delay-once r = TauD (RetD r)

delay-twice : ∀ {R} -> R -> Delay R
delay-twice r = TauD (TauD (TauD (TauD (RetD r))))

-- TREES
record Tree (E : Set₀ -> Set₀) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueT : Σ Set (λ A -> E A × (A -> Tree E R)) ⊎ R

open Tree

TreeRet : ∀ {E} {R} -> R -> Tree E R
ValueT (TreeRet r) = inr r

TreeVis : ∀ {E} {R} -> ∀ {A} -> E A -> (A -> Tree E R) -> Tree E R
ValueT (TreeVis {A = A} e k) = inl (A , e , k)

tree-S : (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ = ℓ-suc ℓ-zero}
tree-S E R = (Container {ℓ = ℓ-zero} -,- λ (x : Container {ℓ = ℓ-zero}) -> R ⊎ Σ Set (λ A -> E A × (A -> M x)))

tree : (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
tree E R = M (tree-S E R)

tree2 : (E : Set₀ -> Set₁) (R : Set₀) -> {t : tree E R} -> Set
tree2 E R {t} = M (out-fun t .fst)

tree-ret : ∀ {E} {R}  -> R -> tree2 E R
tree-ret r = in-fun (r , λ x → {!!})

-- tree-vis : ∀ {E} {R} -> ∀ {A} -> E A -> (A -> tree E R) -> tree E R
-- tree-vis {A = A} e k = out-fun {!!} .snd (A , e , {!!})

-- ITREES
record ITree (E : Set₀ -> Set₁) (R : Set₀) : Set₁ where
  coinductive
  field
    ValueIT : ITree E R ⊎ (Σ Set (λ A -> E A × (A -> ITree E R)) ⊎ R)

-- itree : ∀ {E : Set₀ -> Set₁} {R : Set₀} -> Set₁
-- itree {E} {R} = M (Unit -,- λ { tt -> ? ⊎ (Σ Set (λ A -> E A × (A -> ?)) ⊎ R) } )

open ITree

Ret : {E : Set -> Set₁} {R : Set} -> R -> ITree E R
ValueIT (Ret r) = inr (inr r)

Tau : {E : Set -> Set₁} {R : Set} -> ITree E R -> ITree E R
ValueIT (Tau t) = inl t

Vis : {E : Set -> Set₁} {R : Set} {A : Set} -> E A -> (A -> ITree E R) -> ITree E R
ValueIT (Vis {A = A} e k) = inr (inl (A , e , k))

-- Examples
data IO : Type₀ → Type₁ where
  Input : IO ℕ
  Output : (x : ℕ) -> IO Unit

echo : ITree IO Unit
echo = Vis Input λ x → Vis (Output x) λ x₁ → Tau echo
