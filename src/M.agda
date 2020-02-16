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

record Container : Set₁ where
  constructor _-,-_
  field
    A : Set₀
    B : A -> Set₀

open Container

P₀ : ∀ {S : Container} -> Set₀ -> Set₀
P₀ {S} = λ X -> Σ (A S) λ x → (B S x) -> X

P₁ : ∀ {S : Container} {X Y} -> (f : X -> Y) -> P₀ {S = S} X -> P₀ {S = S} Y
P₁ {S} f = λ { (a , g) -> a , f ∘ g }

Coalg₀ : ∀ {S : Container} -> Set₁
Coalg₀ {S = S} = Σ Set₀ λ C → C → P₀ {S = S} C  

Coalg₁ : ∀ {S : Container} -> Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set₀
Coalg₁ {S = S} (C , γ) (D , δ) = Σ (C → D) λ f → δ ∘ f ≡ (P₁ f) ∘ γ

_⇒_ = Coalg₁

Final : ∀ {S : Container} -> Set₁
Final {S = S} = Σ (Coalg₀ {S = S}) λ X,ρ → ∀ (C,γ : Coalg₀) -> isContr (C,γ ⇒ X,ρ)

record Chain : Set₁ where
  constructor _,,_
  field
    X : ℕ -> Set₀
    π : {n : ℕ} -> X (suc n) -> X n

open Chain

L : Chain → Set
L (x ,, pi) = Σ ((n : ℕ) → x n) λ x → (n : ℕ) → pi {n = n} (x (suc n)) ≡ x n

Cone : ∀ (A : Set₀) -> ∀ (_ : Chain) -> Set₁
Cone A (X ,, pi) = (A → L (X ,, pi)) ≡ (Σ ((n : ℕ) → A → X n) λ f → (n : ℕ) → pi ∘ f (suc n) ≡ f n)

Z = λ (X : ℕ -> Set) (l : ∀ (n : ℕ) -> X n -> X (suc n)) -> Σ ((n : ℕ) → X n) λ x → (n : ℕ) → x (suc n) ≡ l n (x n)

-- lemma11 : ∀ (X : ℕ -> Set) (l : ∀ (n : ℕ) -> X n -> X (suc n)) -> ∀ (f : Z X l -> X 0) -> isEquiv f
-- lemma11 X l f = {!!}

shift-chain : Chain -> Chain
shift-chain = λ X,π -> ((λ x → X X,π (suc x)) ,, λ {n} → π X,π {suc n})

-- Lemma 12
L-unique : {X,π : Chain} -> L (shift-chain X,π) ≡ L X,π
L-unique = {!!}

! : ∀ {A : Set₀} (x : A) -> Unit
! x = tt

sequence-pre₀ : Container -> ℕ -> Set₀
sequence-pre₀ S 0 = Unit
sequence-pre₀ S (suc n) = P₀ {S} (sequence-pre₀ S n)

sequence-pre₁ : (S : Container) -> {n : ℕ} -> sequence-pre₀ S (suc n) -> sequence-pre₀ S n
sequence-pre₁ S {0} = !
sequence-pre₁ S {suc n} = P₁ (sequence-pre₁ S {n})

sequence : Container -> Chain
X (sequence S) n = sequence-pre₀ S n
π (sequence S) {n} = sequence-pre₁ S

M : Container → Set
M = L ∘ sequence

Ms : Container → Set
Ms = L ∘ shift-chain ∘ sequence

L,π : Container -> Container
L,π S = (M S -,- λ x -> X (sequence S) 0)

α : ∀ {c : Chain} -> L c -> L (shift-chain c)
α = {!!}

PX,Pπ : (S : Container) -> Chain
PX,Pπ S = (λ z → P₀ {S} (X (sequence S) z)) ,, λ x → P₁ (λ z → z) (π (sequence S) x) -- TODO: ID func?

-- Lemma 13
α-iso : {S : Container} -> M S ≡ P₀ {S} (L (PX,Pπ S))
α-iso {S} = {!!}

helper : ∀ {S} -> P₀ {S} (L (PX,Pπ S)) ≡ P₀ {S} (M S)
helper {S} = {!!} -- L-unique {sequence S}

shift : ∀ {S : Container} -> M S ≡ P₀ {S} (M S)
shift {S} = λ i -> compPath-filler {x = M S} {y = P₀ {S} (L (PX,Pπ S))} {z = P₀ {S} (M S)} α-iso helper i i

in-fun : ∀ {S : Container} -> P₀ (M S) -> M S
in-fun {k} a = transp (λ i → shift {k} (~ i)) i0 a

out-fun : ∀ {S : Container} -> M S -> P₀ (M S)
out-fun {k} a = transp (λ i → shift {k} i) i0 a

-- Stream example

stream-S : ∀ A -> Container
stream-S A = (A -,- (λ _ → Unit))

stream : ∀ (A : Set₀) -> Set₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> (Unit -> stream A) -> stream A
cons x xs = in-fun (x , xs )

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

record bisim {A} (a : Stream A) (b : stream A) : Set₀ where
  coinductive
  field
    ≈head : head a ≡ hd b
    ≈tail : bisim (tail a) (tl b)

stream-to-Stream : ∀ {A} -> stream A -> Stream A
head (stream-to-Stream s) = hd s
tail (stream-to-Stream s) = stream-to-Stream (tl s)

Stream-to-stream : ∀ {A} -> Stream A -> stream A
Stream-to-stream {A} S = cons (head S) (λ { tt -> Stream-to-stream {A} (tail S) })

stream-equiv : ∀ {A} -> isEquiv (stream-to-Stream {A})
stream-equiv = record { equiv-proof = λ y → ({!!} , {!!}) , λ y₁ i → {!!} , {!!} }

-- itrees (and buildup examples)

-- delay-S : ∀ (R : Set₀) -> Container
-- delay-S R = (Unit -,- λ _ → R ⊎ Unit)

-- delay : ∀ R -> Set₀
-- delay R = M (delay-S R)

-- delay-ret : ∀ {R} -> R -> delay R
-- delay-ret r = out-fun {!!} .snd (inl r)

-- delay-tau : ∀ {R} -> delay R -> delay R
-- delay-tau S = out-fun S .snd (inr tt)


delay-S : ∀ (R : Set₀) -> Container
delay-S R = ((R ⊎ Unit) -,- λ { (inr tt) → Unit ; _ -> R })

delay : ∀ R -> Set₀
delay R = M (delay-S R)

delay-ret : ∀ {R} -> R -> delay R
delay-ret r = in-fun ((inl r) , λ x → {!!})

delay-tau : ∀ {R} -> delay R -> delay R
delay-tau S = in-fun {!!}

-- cons : ∀ {A} -> A -> (Unit -> stream A) -> stream A
-- cons x xs = in-fun (x , xs )

-- hd : ∀ {A} -> stream A -> A
-- hd {A} S = out-fun S .fst

-- tl : ∀ {A} -> stream A -> stream A
-- tl {A} S = out-fun S .snd tt

-- spin : ∀ {A} -> delay A
-- head spin = tt
-- tail spin _ = spin
