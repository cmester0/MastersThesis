{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe
module M where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )

-- Definitions
record Container {ℓ} {ℓ'} : Set (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _-,-_
  field
    A : Set ℓ
    B : A -> Set ℓ'

open Container

P₀ : ∀ {ℓ} {ℓ'} -> ∀ {S : Container {ℓ = ℓ} {ℓ' = ℓ'}} -> Set (ℓ-max ℓ ℓ') -> Set (ℓ-max ℓ ℓ')
P₀ {S = S} = λ X -> Σ (A S) λ x → (B S x) -> X

P₁ : ∀ {ℓ} {ℓ'} {S : Container {ℓ} {ℓ'}} {X Y : Set (ℓ-max ℓ ℓ')} -> (f : X -> Y) -> P₀ {S = S} X -> P₀ {S = S} Y
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

Z = λ {ℓ} (X : ℕ -> Set ℓ) (l : ∀ (n : ℕ) -> X n -> X (suc n)) -> Σ ((n : ℕ) → X n) λ x → (n : ℕ) → x (suc n) ≡ l n (x n)

lemma11 : ∀ {ℓ} (X : ℕ -> Set ℓ) (l : ∀ (n : ℕ) -> X n -> X (suc n)) -> Z X l ≡ X 0 -- ∀ (f : Z X l -> X 0) -> isEquiv f
lemma11 X l f = {!!}

shift-chain : ∀ {ℓ} -> Chain {ℓ} -> Chain {ℓ}
shift-chain = λ X,π -> ((λ x → X X,π (suc x)) ,, λ {n} → π X,π {suc n})

lemma11-helper : ∀ {ℓ} {X,π : Chain {ℓ}} -> ∀ (y : (n : ℕ) -> X X,π n -> X X,π (suc n)) -> Z (X X,π) y ≡ X X,π 0
lemma11-helper {X,π = X,π} = lemma11 (X X,π)

-- (Σ (X X,π 0) λ z -> S z) ≡ 

helper10 : ∀ {ℓ} {X,π : Chain {ℓ}} -> ∀ (S : X X,π 0 -> Set ℓ) -> ((z : X X,π 0) -> isContr (S z)) -> ((Σ (X X,π 0) λ z -> S z) ≡ X X,π 0)
helper10 S cont = λ i → {!!}

helper11 : ∀ {ℓ} {X,π : Chain {ℓ}} -> (y : (n : ℕ) → X X,π (suc n)) -> (z : X X,π 0) -> isContr (π X,π (y 0) ≡ z)
helper11 z = {!!}

helper12 : ∀ {ℓ} {X,π : Chain {ℓ}} -> (y : (n : ℕ) → X X,π (suc n)) -> (Σ (X X,π 0) λ z -> (π X,π (y 0) ≡ z)) ≡ (X X,π 0)
helper12 {X,π = X,π} y = helper10 {X,π = X,π} (λ z → π X,π (y 0) ≡ z) (helper11 {X,π = X,π} y)

helper20 : Unit × Unit ≃ Unit
helper20 = (λ x → tt) , record { equiv-proof = λ { tt → ((tt , tt) , refl) , λ { ( (tt , tt) , r) -> λ i → (tt , tt) , r } } }

helper17 : (Unit × Unit) ≡ Unit
helper17 = ua helper20

helper25 : ∀ {ℓ} {X,π : Chain {ℓ}} (A : Set ℓ) -> ((X X,π 0) × A) ≃ A
helper25 = {!!}

helper26 : ∀ {ℓ} {X,π : Chain {ℓ}} {A B : Set ℓ} -> B ≡ (X X,π 0) -> ((X X,π 0) × A) ≡ A -> (B × A) ≡ A
helper26 p q = λ i -> {!!}

helper14 : ∀ {ℓ} {X,π : Chain {ℓ}} {B : Set ℓ} {A : Set ℓ} -> B ≡ (X X,π 0) -> (B × A) ≡ A
helper14 {X,π = X,π} {A = A} p = λ i ->(helper26 {X,π = X,π} p (ua (helper25 {X,π = X,π} A))) i

helper13 : ∀ {ℓ} {X,π : Chain {ℓ}} -> (Σ ((n : ℕ) → X X,π (suc n)) λ y →                                           ((n : ℕ) → π X,π (y (suc n)) ≡ y n)) ≡
                                      (Σ ((n : ℕ) → X X,π (suc n)) λ y → (Σ (X X,π 0) λ x₀ → (π X,π (y 0) ≡ x₀)) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n))
helper13 {X,π = X,π} = λ i → Σ ((n : ℕ) → X X,π (suc n)) λ y → helper14 {X,π = X,π} {B = Σ (X X,π 0) λ x₀ → π X,π (y 0) ≡ x₀} {A = ((n : ℕ) → π X,π (y (suc n)) ≡ y n)} (helper12 {X,π = X,π} y) (~ i)

helper24 : ∀ {ℓ} {X,π : Chain {ℓ}} {X Y : Set ℓ} {p : X -> Y} {A : ∀ y -> Set ℓ} ->
               (Σ X λ y → (Σ Y λ x₀ → (p y ≡ x₀)) × A y)  ≡
  (Σ Y λ x₀ → (Σ X λ y →              (p y ≡ x₀)  × A y))
helper24 = {!!}

helper23 : ∀ {ℓ} {X,π : Chain {ℓ}} {A : ∀ y -> Set ℓ} ->
                      (Σ ((n : ℕ) → X X,π (suc n)) λ y → (Σ (X X,π 0) λ x₀ → (π X,π (y 0) ≡ x₀)) × A y) ≡
  (Σ (X X,π 0) λ x₀ → (Σ ((n : ℕ) → X X,π (suc n)) λ y →                     (π X,π (y 0) ≡ x₀) × A y))
helper23 {X,π = X,π} = helper24 {X,π = X,π}

helper15 : ∀ {ℓ} {X,π : Chain {ℓ}} -> (                    Σ ((n : ℕ) → X X,π (suc n)) λ y → (Σ (X X,π 0) λ x₀ → (π X,π (y 0) ≡ x₀)) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n)) ≡
                                       (Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y →                      (π X,π (y 0) ≡ x₀)  × ((n : ℕ) → π X,π (y (suc n)) ≡ y n))
helper15 {X,π = X,π} = λ i → helper23 {X,π = X,π} {A = λ y → (n : ℕ) → π X,π (y (suc n)) ≡ y n} i

helper0 : ∀ {ℓ} {X,π : Chain {ℓ}} -> (                    Σ ((n : ℕ) → X X,π (suc n)) λ y →                      ((n : ℕ) → π X,π (y (suc n)) ≡ y n)) ≡
                                      (Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n))
helper0 {X,π = X,π} =
  λ i → compPath-filler
    {x = Σ ((n : ℕ) → X X,π (suc n)) λ y → (n : ℕ) → π X,π (y (suc n)) ≡ y n}
    {y = Σ ((n : ℕ) → X X,π (suc n)) λ y → (Σ (X X,π 0) (λ x₀ → π X,π (y 0) ≡ x₀)) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n)}
    {z = Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n)}
    (helper13 {X,π = X,π})
    (helper15 {X,π = X,π})
    i i

helper1 : ∀ {ℓ} {X,π : Chain {ℓ}} -> (Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n)) ≡
                                      (                   Σ ((n : ℕ) → X X,π n)      λ x → (π X,π (x 1) ≡ x 0) × ((n : ℕ) → π X,π (x (suc (suc n))) ≡ x (suc n))) -- π X,π (x 0) ≡ x 0 ?????
                                                                           ---- ^ should be a zero , by paper !! (this is wrong!)
helper1 = λ i → {!!}

helper2 : ∀ {ℓ} {X,π : Chain {ℓ}} -> (Σ ((n : ℕ) → X X,π n) λ x → (π X,π (x 1) ≡ x 0) × ((n : ℕ) → π X,π (x (suc (suc n))) ≡ x (suc n))) ≡
                                      L X,π
helper2 = λ i → {!!}

-- Lemma 12
L-unique : ∀ {ℓ} -> {X,π : Chain {ℓ}} -> L (shift-chain X,π) ≡ L X,π
L-unique {X,π = X,π} = λ i →
  compPath-filler
    {x = L (shift-chain X,π)}
    {y = Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n)} 
    {z = L X,π}
    (helper0 {X,π = X,π})
    (λ j ->
      compPath-filler
        {x = Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n)}
        {y = Σ ((n : ℕ) → X X,π n) λ x → (π X,π (x 1) ≡ x 0) × ((n : ℕ) → π X,π (x (suc (suc n))) ≡ x (suc n))} 
        {z = L X,π}
        (helper1 {X,π = X,π})
        (helper2 {X,π = X,π})
        j j)
    i i

! : ∀ {ℓ} {A : Set ℓ} (x : A) -> Lift {ℓ-zero} {ℓ} Unit
! x = lift tt

sequence-pre₀ : ∀ {ℓ} {ℓ'} -> Container {ℓ} {ℓ'} -> ℕ -> Set (ℓ-max ℓ ℓ')
sequence-pre₀ S 0 = Lift Unit
sequence-pre₀ S (suc n) = P₀ {S = S} (sequence-pre₀ S n)

sequence-pre₁ : ∀ {ℓ} {ℓ'} -> (S : Container {ℓ} {ℓ'}) -> {n : ℕ} -> sequence-pre₀ S (suc n) -> sequence-pre₀ S n
sequence-pre₁ {ℓ} {ℓ'} S {0} = ! {ℓ-max ℓ ℓ'}
sequence-pre₁ S {suc n} = P₁ (sequence-pre₁ S {n})

sequence : ∀ {ℓ} {ℓ'} -> Container {ℓ} {ℓ'} -> Chain {ℓ-max ℓ ℓ'}
X (sequence {ℓ} {ℓ'} S) n = sequence-pre₀ {ℓ} {ℓ'} S n
π (sequence {ℓ} {ℓ'} S) {n} = sequence-pre₁ {ℓ} S

M : ∀ {ℓ} {ℓ'} -> Container {ℓ} {ℓ'} → Set (ℓ-max ℓ ℓ')
M = L ∘ sequence

PX,Pπ : ∀ {ℓ} {ℓ'} (S : Container {ℓ} {ℓ'}) -> Chain
PX,Pπ {ℓ} {ℓ'} S = (λ z → P₀ {S = S} (X (sequence S) z)) ,, (λ x → P₁ {ℓ} {ℓ'} (λ z → z) (π (sequence S) x)) -- TODO: Id func?

-- Lemma 13
α-iso : ∀ {ℓ} {ℓ'} {S : Container {ℓ} {ℓ'}} -> M S ≡ P₀ {S = S} (L (PX,Pπ S))
α-iso {S = S} = {!!}

helper : ∀ {ℓ} {ℓ'} {S} -> P₀ {ℓ} {ℓ'} {S = S} (L (PX,Pπ S)) ≡ P₀ {S = S} (M S)
helper {ℓ} {S = S} = {!!} -- λ i → P₀ {ℓ} (L-unique {ℓ} {X,π = sequence {ℓ} S} i)

-- P commutes with limits
shift : ∀ {ℓ} {ℓ'} {S : Container {ℓ} {ℓ'}} -> M S ≡ P₀ {S = S} (M S)
shift {S = S} = λ i -> compPath-filler {x = M S} {y = P₀ {S = S} (L (PX,Pπ S))} {z = P₀ {S = S} (M S)} α-iso helper i i

in-fun : ∀ {ℓ} {ℓ'} {S : Container {ℓ} {ℓ'}} -> P₀ {S = S} (M S) -> M S
in-fun {S = S} a = transp (λ i → shift {S = S} (~ i)) i0 a

out-fun : ∀ {ℓ} {ℓ'} {S : Container {ℓ} {ℓ'}} -> M S -> P₀ {S = S} (M S)
out-fun {S = S} a = transp (λ i → shift {S = S} i) i0 a

-- bisimulation (TODO)
-- record bisimulation {ℓ} {ℓ'} (S : Container {ℓ} {ℓ'}) (R : Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set₀) : Set₁ where
--   field
--     αᵣ : let R⁻ = Σ (Coalg₀ {S}) (λ a -> Σ (Coalg₀ {S}) (λ b -> R a b)) in R⁻ -> P₀ {S = {!!}} R⁻

-- coinduction : ∀ (S : Container) -> ∀ (R : Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set₀) -> bisimulation S R -> ∀ m m' -> R m m' -> m ≡ m'
-- coinduction S R x m m' rel = λ i → {!!}


