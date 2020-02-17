{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe
module M where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )

-- Definitions
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

helper0 : ∀ {ℓ} {X,π : Chain {ℓ}} -> L (shift-chain X,π) ≡ (Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n))
helper0 = λ i → {!!}

helper1 : ∀ {ℓ} {X,π : Chain {ℓ}} -> (Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n)) ≡
                                      (Σ ((n : ℕ) → X X,π n) λ x → (π X,π (x 1) ≡ x 0) × ((n : ℕ) → π X,π (x (suc (suc n))) ≡ x (suc n))) -- π X,π (x 0) ≡ x 0 ?????
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

PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
PX,Pπ S = (λ z → P₀ {S = S} (X (sequence S) z)) ,, (λ x → P₁ (λ z → z) (π (sequence S) x)) -- TODO: Id func?

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> M S ≡ P₀ {S = S} (L (PX,Pπ S))
α-iso {S = S} = {!!}

helper : ∀ {ℓ} {S} -> P₀ {ℓ} {S = S} (L (PX,Pπ S)) ≡ P₀ {S = S} (M S)
helper {ℓ} {S = S} = {!!} -- λ i → P₀ {ℓ} (L-unique {ℓ} {X,π = sequence {ℓ} S} i)

-- P commutes with limits
shift : ∀ {ℓ} {S : Container {ℓ}} -> M S ≡ P₀ {S = S} (M S)
shift {S = S} = λ i -> compPath-filler {x = M S} {y = P₀ {S = S} (L (PX,Pπ S))} {z = P₀ {S = S} (M S)} α-iso helper i i

in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ {S = S} (M S) -> M S
in-fun {S = S} a = transp (λ i → shift {S = S} (~ i)) i0 a

out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M S -> P₀ {S = S} (M S)
out-fun {S = S} a = transp (λ i → shift {S = S} i) i0 a

-- bisimulation (TODO)
record bisimulation (S : Container) (R : Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set₀) : Set₁ where
  field
    αᵣ : let R⁻ = Σ (Coalg₀ {S}) (λ a -> Σ (Coalg₀ {S}) (λ b -> R a b)) in R⁻ -> P₀ {S = {!!}} R⁻

coinduction : ∀ (S : Container) -> ∀ (R : Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set₀) -> bisimulation S R -> ∀ m m' -> R m m' -> m ≡ m'
coinduction S R x m m' rel = λ i → {!!}


