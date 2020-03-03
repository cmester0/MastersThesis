{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe

open import M

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )

open import Cubical.Data.Unit

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

module Coalg where

-------------------------------
-- Definition of a Coalgebra --
-------------------------------

Coalg₀ : ∀ {ℓ} {S : Container {ℓ}} -> Set (ℓ-suc ℓ)
Coalg₀ {ℓ} {S = S} = Σ (Set ℓ) λ C → C → P₀ {S = S} C  

Coalg₁ : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S} -> Coalg₀ {S = S} -> Set ℓ
Coalg₁ {S = S} (C , γ) (D , δ) = Σ (C → D) λ f → δ ∘ f ≡ (P₁ f) ∘ γ

-- Coalgebra morphism notation
_⇒_ = Coalg₁

-----------------------------------------------------------------------------
-- The limit of a Polynomial functor over a Container is a Final Coalgebra --
-----------------------------------------------------------------------------

Ps : ∀ {ℓ} -> (S : Container {ℓ}) -> (C,γ : Coalg₀ {S = S}) -> Container {ℓ}
Ps S T = T .fst , λ x → P₀ {S = S}  (T .fst)

Ms : ∀ {ℓ} -> (S : Container {ℓ}) -> Container {ℓ}
Ms S = M S , λ x → P₀ {S = S}  (M S)

M-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S}
M-coalg {S = S} = (M S) , out-fun

PM-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S}
PM-coalg {S = S} = (P₀ (M S)) , P₁ out-fun

Final : ∀ {ℓ} {S : Container {ℓ}} -> Set (ℓ-suc ℓ)
Final {S = S} = Σ (Coalg₀ {S = S}) λ X,ρ → ∀ (C,γ : Coalg₀ {S = S}) -> isContr (_⇒_ {S = S} (C,γ) (X,ρ))

-------------------------------
-- Bisimilarity of Coalgebra --
-------------------------------

record _≈_ {ℓ} {S : Container {ℓ}} (a b : M S) : Set (ℓ-suc ℓ) where
  coinductive
  field
    head≈ : out-fun a .fst ≡ out-fun b .fst
    tails≈ : ∀ (pa : S .snd (out-fun a .fst)) (pb : S .snd (out-fun b .fst)) -> out-fun {S = S} a .snd pa ≈ out-fun {S = S} b .snd pb

open _≈_ public

-- Strong bisimulation ?
record bisimulation {ℓ} (S : Container {ℓ}) (C,γ : Coalg₀ {S = S}) (R : C,γ .fst -> C,γ .fst -> Set ℓ) : Set (ℓ-suc ℓ) where  
  coinductive
  -- field R : C,γ .fst -> C,γ .fst -> Set ℓ
  
  R⁻ = Σ (C,γ .fst) (λ a -> Σ (C,γ .fst) (λ b -> R a b))

  π₁ : R⁻ -> C,γ .fst
  π₁ = fst
  
  π₂ : R⁻ -> C,γ .fst
  π₂ = fst ∘ snd
  
  field
    αᵣ : R⁻ -> P₀ {S = S} R⁻
    rel₁ : (C,γ .snd) ∘ π₁ ≡ P₁ π₁ ∘ αᵣ
    rel₂ : (C,γ .snd) ∘ π₂ ≡ P₁ π₂ ∘ αᵣ

  R⁻-coalg : Coalg₀
  R⁻-coalg = R⁻ , αᵣ
  
  prod₁ : R⁻-coalg ⇒ C,γ
  prod₁ = π₁ , rel₁
  
  prod₂ : R⁻-coalg ⇒ C,γ
  prod₂ = π₂ , rel₂

open bisimulation public

record equality-relation {A : Set} (R : A -> A -> Set) : Set where
  field
    eq-refl : ∀ {x} -> R x x
    eq-sym : ∀ {x y} -> R x y -> R y x
    eq-trans : ∀ {x y z} -> R x y -> R y z -> R x z

open equality-relation

record eq+anti {A : Set} (R : A -> A -> Set) : Set where
  field
    eq-rel : equality-relation R
    eq-anti : ∀ {x y} -> R x y -> R y x -> x ≡ y

-- equality-relation-projection-helper : ∀ {A R} (eq : equality-relation R) (x y : A) -> R x y -> x ≡ y
-- equality-relation-projection-helper eq x y rel = λ i → {!!}

-- equality-relation-projection : ∀ {A R} (eq : equality-relation R) -> (x : Σ A (λ a → Σ A (R a))) -> (fst x) ≡ (fst (x .snd))
-- equality-relation-projection {A = A} {R = R} eq (x , y , p) = λ i → cong (λ a → {!!}) {!!} i

postulate
  equality-relation-projection : ∀ {A R} (eq : equality-relation R) -> (x : Σ A (λ a → Σ A (R a))) -> (fst x) ≡ (fst (x .snd))
  equality-mono : ∀ {A R} (eq : equality-relation R) (f : A -> A) (x y : A) -> R x y → R (f x) (f y)
  
--------------------------------------------------------
-- Properties of Bisimulations and (Final) Coalgebras --
--------------------------------------------------------

unfold : ∀ {ℓ} {S : Container {ℓ}} -> (X,ρ : Final {S = S}) -> (C,γ : Coalg₀ {S = S}) -> (_⇒_ {S = S} (C,γ) (X,ρ .fst))  -- unique function into final coalg
unfold X,ρ C,γ = X,ρ .snd C,γ .fst

unfold-function : ∀ {ℓ} {S : Container {ℓ}} -> (X,ρ : Final {S = S}) -> (C,γ : Coalg₀ {S = S}) -> (C,γ .fst) -> (X,ρ .fst .fst)  -- unique function into final coalg
unfold-function X,ρ C,γ y = (unfold X,ρ C,γ) .fst y

U : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Set ℓ
U {S = S} {C,γ = C,γ} = Σ (C,γ .fst -> M S) λ f → out-fun ∘ f ≡ P₁ f ∘ C,γ .snd

-- U-is-Unit : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> (U {C,γ = C,γ} ≡ Lift Unit)
-- U-is-Unit = λ i → {!!}

postulate -- TODO
  U-is-Unit : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> (U {C,γ = C,γ} ≡ Lift Unit)

contr-is-ext : ∀ {ℓ} {A B : Set ℓ} -> A ≡ B -> isContr A ≡ isContr B
contr-is-ext p = λ i -> isContr (p i)
  
U-contr : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ∀ (x : U {C,γ = C,γ}) -> isContr (U {C,γ = C,γ})
U-contr {ℓ} {C,γ = C,γ} x = transp (λ i -> (sym (contr-is-ext {A = U {C,γ = C,γ}} U-is-Unit)) i) i0 (lift tt , λ { (lift tt) -> refl })

----------------------------------------------------
-- Finality properties for bisimulation relations --
----------------------------------------------------

M-final-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Final {S = S}
M-final-coalg {ℓ} {S = S} = M-coalg , λ C,γ → transp (λ i → (sym (U-is-Unit {C,γ = C,γ})) i) i0 (lift tt) , λ y → U-contr {C,γ = C,γ} y .snd y

final-coalg-property-2 : ∀ {ℓ} {S : Container {ℓ}} -> (C : Coalg₀ {S = S}) -> (F : Final {S = S}) -> ∀ (f g : C ⇒ F .fst) -> f ≡ g
final-coalg-property-2 C F f g = λ i -> compPath-filler (sym (F .snd C .snd f))  (F .snd C .snd g) i i -- follows from contractability

final-property : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> prod₁ sim ≡ prod₂  sim
final-property S R sim = final-coalg-property-2 {S = S} (R⁻-coalg sim) (M-final-coalg {S = S}) (prod₁ sim) (prod₂ sim)

final-property-2 : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> π₁ sim ≡ π₂  sim
final-property-2 S R sim = λ i -> final-property S R sim i .fst

-------------------------------------------------------------
-- Coinduction principle for M-types (≈ Coinductive types) --
-------------------------------------------------------------

-- coinduction proof by: m ≡ π₁(m,m',r) ≡ π₂(m,m',r) ≡ m' 
coinduction : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> ∀ {m m' : M S} -> R m m' -> m ≡ m' 
coinduction {S = S} R sim {m} {m'} r = λ i -> funExt⁻ (final-property-2 S R sim) (m , (m' , r)) i

coinduction⁻ : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (∀ {x} -> R x x) ->  ∀ {m m' : M S} -> m ≡ m' -> R m m'
coinduction⁻ {S = S} R sim k {m} {m'} r = transp (λ i -> R m (r i)) i0 k

coinduction-iso1 : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (R-refl : ∀ {x} -> R x x) ->
                     ∀ {m} {m'} (p : m ≡ m') -> (coinduction R sim {m} {m'}) (coinduction⁻ R sim R-refl p) ≡ p
coinduction-iso1 R sim R-refl p = {!!}

coinduction-iso2 : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (R-refl : ∀ {x} -> R x x) ->
                     ∀ {m} {m'} (p : R m m') -> (coinduction⁻ R sim R-refl (coinduction R sim {m} {m'} p)) ≡ p
coinduction-iso2 R sim R-refl p = {!!}

coinduction-is-equality : ∀ {ℓ} {S : Container {ℓ}} R ->
  (sim : bisimulation S M-coalg R) ->
  (R-refl : ∀ {x} -> R x x) ->
  R ≡ _≡_
coinduction-is-equality R sim R-refl i m m' =
  ua (isoToEquiv (
    iso
      (coinduction R sim {m} {m'})
      (coinduction⁻ R sim R-refl)
      (coinduction-iso1 R sim R-refl)
      (coinduction-iso2 R sim R-refl)
    )) i
