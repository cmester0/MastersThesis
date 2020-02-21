{-# OPTIONS --cubical --guardedness #-} --safe

module itree3 where

open import Cubical.Codata.M

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

data ⊥₁ : Set₁ where

itree-S : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> IxCont (Lift Unit) -- Unit because we don't need indexing
itree-S E R = ((λ _ → (Unit ⊎ R) ⊎ Σ Set E) , λ _ -> λ { (inl (inl _)) _ → Lift Unit
                                                         ; (inl (inr _)) _ -> ⊥₁
                                                         ; (inr (A , _)) _ -> Lift A} )

itree : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
itree E R = M (itree-S E R) _

Tau : {E : Set₀ -> Set₁} -> {R : Set₀} -> itree E R -> itree E R
Tau t = inM _ ((inl (inl tt)) , λ _ _ → t)

Vis : ∀ {E} {R}  -> ∀ {A} -> E A -> (A -> itree E R) -> itree E R
Vis {A = A} e k = inM _ (inr (A , e) , λ { _ (lift x) -> k x } )

Ret : ∀ {E} {R}  -> R -> itree E R
Ret {E} {R} r = inM _ (inl (inr r) , λ _ ())

-- Bind operations

record monad (M : Set -> Set) : Set₁ where
  field
    ret : ∀ {A} → A → M A
    bind : ∀ {A B} -> M A -> (A -> M B) -> M B

open monad

delay-S : ∀ (R : Set₀) -> IxCont Unit -- Unit because we don't need indexing
delay-S R = ((λ _ → Unit ⊎ R) , λ _ -> λ { (inl _) _ → Unit
                                           ; (inr _) _ -> ⊥ } )

delay : ∀ (R : Set₀) -> Set
delay R = M (delay-S R) _

record delay2 (R : Set) : Set where
  coinductive
  field
    ValueD : delay2 R ⊎ R

open delay2

delay-to-delay2 : {R : Set} -> delay R -> delay2 R
ValueD (delay-to-delay2 k) = case (unfold {!!} {!!} k) of {!!}

bind'' : ∀ {A B} -> delay2 A -> (A -> delay2 B) -> delay2 B
ValueD (bind'' S k) = case ValueD S of λ { (inl t) → inl (bind'' t k)
                                         ; (inr r) -> ValueD (k r) }

delay-ret : ∀ {R}  -> R -> delay R
delay-ret {R} r = inM _ (inr r , λ _ ())

delay-tau : ∀ {R}  -> delay R -> delay R
delay-tau {R} t = inM _ (inl _ , λ _ _ -> t)

delay-tau-S : ∀ {R : Set}  -> Unit ⊎ R -> Unit ⊎ R
delay-tau-S {R} t = inl _

bind' : ∀ {A B} -> delay A -> (A -> delay B) -> delay B
bind' e k = {!!}

delay-monad : monad delay
ret (delay-monad) a = delay-ret a
bind (delay-monad) e k = record { head = inl tt ; tails = λ _ _ → case head e of λ { (inl _) → {!!}
                                                                                    ; (inr r) → {!!} } }

-- itree-monad : ∀ {E} -> monad (itree E)
-- ret (itree-monad) a = Ret a
-- bind (itree-monad) e k = {!!}

-- bind : ∀ {E} {R} {S} -> itree E R -> (R -> itree E S) -> itree E S
-- bind {E} {R} {S} t k = bind-helper k (out-fun {S = itree-S E R} t .fst)

-- trigger : ∀ {E R} -> E R -> itree E R
-- trigger e = vis e λ x → ret x
