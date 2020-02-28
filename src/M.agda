{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe
module M where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )

open import Cubical.Foundations.Transport

Container : ∀ {ℓ} -> Set (ℓ-suc ℓ)
Container {ℓ} = Σ (Set ℓ) (λ A -> A -> Set ℓ)

P₀ : ∀ {ℓ} {S : Container {ℓ}} -> Set ℓ -> Set ℓ
P₀ {S = S} X  = Σ (S .fst) λ x → (S .snd x) -> X

P₁ : ∀ {ℓ} {S : Container {ℓ}} {X Y} (f : X -> Y) -> P₀ {S = S} X -> P₀ {S = S} Y
P₁ {S = S} f = λ { (a , g) ->  a , f ∘ g }

record Chain {ℓ} : Set (ℓ-suc ℓ) where
  constructor _,,_
  field
    X : ℕ -> Set ℓ
    π : {n : ℕ} -> X (suc n) -> X n

open Chain

L : ∀ {ℓ} -> Chain {ℓ} → Set ℓ
L (x ,, pi) = Σ ((n : ℕ) → x n) λ x → (n : ℕ) → pi {n = n} (x (suc n)) ≡ x n

shift-chain : ∀ {ℓ} -> Chain {ℓ} -> Chain {ℓ}
shift-chain = λ X,π -> ((λ x → X X,π (suc x)) ,, λ {n} → π X,π {suc n})

intro-helper : ∀ {ℓ} {X Y : Set ℓ} (p : X -> Set ℓ) (q : X -> Y -> Set ℓ) -> Σ Y (λ b → ∀ a -> q a b) -> (Σ X λ a -> p a) ≃ (Σ Y (λ b -> Σ X λ a -> q a b × p a))
intro-helper p q y = (λ x → y .fst , x .fst , y .snd (x .fst) , x .snd) , record { equiv-proof = λ y₁ → (({!!} , {!!}) , {!!}) , λ y₂ i → {!!} }

intro : ∀ {ℓ} {X Y : Set ℓ} (p : X -> Set ℓ) (q : X -> Y -> Set ℓ) -> (Σ X λ a -> p a) ≡ (Σ Y (λ b -> Σ X λ a -> q a b × p a))
intro p q = λ i → {!!}

postulate -- TODO
  combine : ∀ {ℓ} (X : ℕ -> Set ℓ) (p : ∀ {n} -> (X (suc n)) -> (X n) -> Set ℓ)  ->
    (Σ (X 0) λ x₀ → Σ ((n : ℕ) → X (suc n)) λ y → (p (y 0) x₀) × ((n : ℕ) → p (y (suc n)) (y n))) ≡
                   (Σ ((n : ℕ) → X n)       λ x → (p (x 1) (x 0)) × ((n : ℕ) → p (x (suc (suc n))) (x (suc n))))

  -- intro : ∀ {ℓ} {X Y : Set ℓ} (p : X -> Set ℓ) (q : X -> Y -> Set ℓ) -> (Σ X λ a ->         p a) ≡
  --                                                            (Σ Y (λ b -> Σ X λ a -> q a b × p a))
                                                             
  combine2 : ∀ {ℓ} (X : ℕ -> Set ℓ) -> (p : ∀ {n} -> (X (suc n)) -> (X n) -> Set ℓ) -> (y : (n : ℕ) -> X n) ->
    p (y 1) (y 0) × ((n : ℕ) → p (y (suc (suc n))) (y (suc n))) ≡ ((n : ℕ) → p (y (suc n)) (y n))

-- Lemma 12
L-unique : ∀ {ℓ} -> {X,π : Chain {ℓ}} -> L (shift-chain X,π) ≡ L X,π
L-unique {X,π = X,π} = λ i →
  compPath-filler
    {x = L (shift-chain X,π)}
    {y = Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n)} 
    {z = L X,π}
    (intro {X = ((n : ℕ) → X X,π (suc n))} {Y = (X X,π 0)} (λ y → (n : ℕ) → π X,π (y (suc n)) ≡ y n) λ y x₀ → π X,π (y 0) ≡ x₀)
    (λ j ->
      compPath-filler
        {x = Σ (X X,π 0) λ x₀ → Σ ((n : ℕ) → X X,π (suc n)) λ y → (π X,π (y 0) ≡ x₀) × ((n : ℕ) → π X,π (y (suc n)) ≡ y n)}
        {y = Σ ((n : ℕ) → X X,π n) λ x → (π X,π (x 1) ≡ x 0) × ((n : ℕ) → π X,π (x (suc (suc n))) ≡ x (suc n))} 
        {z = L X,π}
        (combine (X X,π) λ a b -> π X,π a ≡ b)
        (λ i → Σ ((n : ℕ) → X X,π n) λ x → combine2 (X X,π) (λ a b → π X,π a ≡ b) x i)
        j j)
    i i

! : ∀ {ℓ} {A : Set ℓ} (x : A) -> Lift {ℓ-zero} {ℓ} Unit
! x = lift tt

sequence-pre₀ : ∀ {ℓ} -> Container {ℓ} -> ℕ -> Set ℓ -- (ℓ-max ℓ ℓ')
sequence-pre₀ S 0 = Lift Unit
sequence-pre₀ S (suc n) = P₀ {S = S} (sequence-pre₀ S n)

sequence-pre₁ : ∀ {ℓ} -> (S : Container {ℓ}) -> {n : ℕ} -> sequence-pre₀ S (suc n) -> sequence-pre₀ S n
sequence-pre₁ {ℓ} S {0} = ! {ℓ}
sequence-pre₁ S {suc n} = P₁ (sequence-pre₁ S {n})

sequence : ∀ {ℓ} -> Container {ℓ} -> Chain {ℓ}
X (sequence {ℓ} S) n = sequence-pre₀ {ℓ} S n
π (sequence {ℓ} S) {n} = sequence-pre₁ {ℓ} S {n}

M : ∀ {ℓ} -> Container {ℓ} → Set ℓ
M = L ∘ sequence

PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
PX,Pπ {ℓ} S =
  (λ n → P₀ {S = S} (X (sequence S) n)) ,,
  (λ {n : ℕ} x → P₁ (λ z → z) (π (sequence S) {n = suc n} x ))

postulate -- TODO
  swap-Σ-∀ : ∀ {ℓ} (X : ℕ -> Set ℓ) (A : Set ℓ) (B : A -> Set ℓ) (p : {n : ℕ} -> Σ A (λ a -> B a -> X (suc n)) -> Σ A (λ a -> B a -> X n) -> Set ℓ) ->
    (Σ (∀ (n : ℕ) -> Σ A (λ a -> B a -> X n)) (λ w -> (n : ℕ) -> p (w (suc n)) (w n))) ≡
    (Σ ((n : ℕ) → A) λ a → Σ ((n : ℕ) → B (a n) → X n) λ u → (n : ℕ) -> p (a (suc n) , u (suc n)) (a n , u n))  

  todo-rules : ∀ {ℓ} (S : Container {ℓ}) -> (Σ ((n : ℕ) → S .fst) λ a → Σ ((n : ℕ) → S .snd (a n) → X (sequence S) n) λ u → (n : ℕ) -> P₁ {S = S} (π (sequence S) {n = n}) (a (suc n) , u (suc n)) ≡ (a n , u n)) ≡ P₀ {S = S} (M S)
  -- equality of pairs, lemma 11, (Universal property of L)

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
α-iso {S = S} = λ i ->
  compPath-filler
    {x = L (PX,Pπ S)}
    {y = (Σ ((n : ℕ) → S .fst) λ a → Σ ((n : ℕ) → S .snd (a n) → X (sequence S) n) λ u → (n : ℕ) -> P₁ (π (sequence S) {n}) (a (suc n) , u (suc n)) ≡ (a n , u n))}
    {z = P₀ {S = S} (M S)}
      (swap-Σ-∀ (X (sequence S)) (S .fst) (S .snd) λ {n} a b → (P₁ (π (sequence S) {n = n})) a ≡ b)
      (todo-rules S)
      i i

-- P commutes with limits
shift : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M S) ≡ M S
shift {S = S} = λ i ->
  compPath-filler
    {x = P₀ (M S)}
    {y = L (PX,Pπ S)}
    {z = M S}
      (sym α-iso)                   -- lemma 13
      (L-unique {X,π = sequence S}) -- lemma 12
      i i
      
in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M S) -> M S
in-fun {S = S} = transport (shift {S = S})

out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M S -> P₀ (M S)
out-fun {S = S} = transport (sym (shift {S = S}))

out-inverse-in : ∀ {ℓ} {S : Container {ℓ}} -> (out-fun ∘ in-fun {S = S}) ≡ (λ x -> x)
out-inverse-in i a = transport⁻Transport shift a i

out-inverse-in-x : ∀ {ℓ} {S : Container {ℓ}} -> ∀ x -> (out-fun ∘ in-fun {S = S}) x ≡ x
out-inverse-in-x = funExt⁻ out-inverse-in

in-inverse-out : ∀ {ℓ} {S : Container {ℓ}} -> (in-fun ∘ out-fun {S = S}) ≡ (λ (x : M S) -> x)
in-inverse-out = λ i a → transportTransport⁻ shift a i

in-inverse-out-x : ∀ {ℓ} {S : Container {ℓ}} -> ∀ x -> (in-fun ∘ out-fun {S = S}) x ≡ x
in-inverse-out-x = funExt⁻ in-inverse-out
