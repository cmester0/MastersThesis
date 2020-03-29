{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Prod

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Embedding

open import helper

module Coalg.Properties where

open import Coalg.Base
open import Container
open import M

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

--------------------------------------------------------
-- Properties of Bisimulations and (Final) Coalgebras --
--------------------------------------------------------

coalg-unfold : ∀ {ℓ} {S : Container {ℓ}} -> (X,ρ : Final {S = S}) -> (C,γ : Coalg₀ {S = S}) -> (_⇒_ {S = S} (C,γ) (X,ρ .fst))  -- unique function into final coalg
coalg-unfold X,ρ C,γ = X,ρ .snd C,γ .fst

coalg-unfold-function : ∀ {ℓ} {S : Container {ℓ}} -> (X,ρ : Final {S = S}) -> (C,γ : Coalg₀ {S = S}) -> (C,γ .fst) -> (X,ρ .fst .fst)  -- unique function into final coalg
coalg-unfold-function X,ρ C,γ y = (coalg-unfold X,ρ C,γ) .fst y

U : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Set ℓ
U {S = S} {C,γ = C,γ} = Σ (C,γ .fst -> M S) λ f → out-fun ∘ f ≡ P₁ f ∘ C,γ .snd

open Iso

FunctionToProjection : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀) -> Cone C,γ -> C,γ .fst -> M S
FunctionToProjection {S = S} C,γ = inv (lemma10-Iso {C,γ = C,γ})

step : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} {Y : Set ℓ} (f : C,γ .fst -> Y) → C,γ .fst → P₀ Y
step {C,γ = C,γ} {Y = Y} f = P₁ f  ∘ C,γ .snd

Ψ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} (f : C,γ .fst -> M S) -> C,γ .fst -> M S
Ψ {C,γ = C,γ} f = in-fun ∘ step {C,γ = C,γ} f

ϕ₀ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} (u : (n : ℕ) → C,γ .fst → X (sequence S) n) -> (n : ℕ) -> C,γ .fst -> W S n
ϕ₀ u 0 = λ x -> lift tt
ϕ₀ {C,γ = C,γ} u (suc n) = step {C,γ = C,γ} (u n)

ϕ₁ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}}
           (u : (n : ℕ) → C,γ .fst → X (sequence S) n) ->
           (g : (n : ℕ) → π (sequence S) ∘ u (suc n) ≡ u n) ->
           (n : ℕ) → π (sequence S) ∘ (ϕ₀ {C,γ = C,γ} u (suc n)) ≡ ϕ₀ {C,γ = C,γ} u n
ϕ₁ u g 0 i = !
ϕ₁ {S = S} {C,γ = C,γ'} u g (suc n) = λ i a → step {C,γ = C,γ'} (λ x → g n i x) a

Φ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Cone C,γ -> Cone C,γ
Φ {S = S} {C,γ = C,γ} (u , g) = ϕ₀ {C,γ = C,γ} u , ϕ₁ {S = S} {C,γ = C,γ} u g

postulate
  commutivity : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}}
    → let e = FunctionToProjection C,γ in
    Ψ {C,γ = C,γ} ∘ e ≡ e ∘ Φ {C,γ = C,γ}

e-inj : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} {x y}
  → (FunctionToProjection C,γ x ≡ FunctionToProjection C,γ y)
  ≡ (x ≡ y)
e-inj {C,γ = C,γ} = ≡-rel-b-inj-x (lemma10-Iso {C,γ = C,γ})

u0 : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Cone₀ {C,γ = C,γ}
u0 {C,γ = C,γ} = λ { 0 _ → lift tt ; (suc n) -> step {C,γ = C,γ} (u0 {C,γ = C,γ} n) }

p0 : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> (n : ℕ) → u0 {C,γ = C,γ} n ≡ ϕ₀ {C,γ = C,γ} (u0 {C,γ = C,γ}) n
p0 0 = refl
p0 (suc n) = refl

-- Lemma 11 should be used somewhere about here
postulate
  missing-0-helper : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> (b : Σ (Cone₀ {C,γ = C,γ}) (λ u → u ≡ ϕ₀ {C,γ = C,γ} u)) -> (u0 , funExt p0) ≡ b

missing-0 : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Lift Unit ≡ Σ (Cone₀ {C,γ = C,γ}) (λ u → u ≡ ϕ₀ {C,γ = C,γ} u)
missing-0 {S = S} = isoToPath (iso (λ _ → u0 , (funExt p0)) (λ x → lift tt) (λ b → missing-0-helper b) λ a i → lift tt)

postulate
  missing-2 : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ((x : Lift Unit) → Lift {ℓ-zero} {ℓ} Unit ≡ (Σ (Cone₁ {C,γ = C,γ} ((transport (missing-0 {C,γ = C,γ}) x) .fst)) (λ q → PathP (λ i → Cone₁ {C,γ = C,γ} ((transport (missing-0 {C,γ = C,γ}) x) .snd i)) q (ϕ₁ {C,γ = C,γ} ((transport (missing-0 {C,γ = C,γ}) x) .fst) q))))

U-is-Unit-Iso :
  ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S})
  ------------------------------------
  → Iso (C,γ ⇒ M-coalg) (Lift Unit)
U-is-Unit-Iso {ℓ = ℓ} {S = S} C,γ@(C , γ) =
  let e = FunctionToProjection C,γ in
  let 𝓛 = M S in
  U {C,γ = C,γ}
    Iso⟨ refl-iso ⟩
  Σ (C → 𝓛) (λ f → out-fun ∘ f ≡ step {C,γ = C,γ} f)
    Iso⟨ Σ-ap-iso₂ (λ f → sym-iso (pathToIso in-inj)) ⟩
  Σ (C → 𝓛) (λ f → in-fun ∘ out-fun ∘ f ≡ in-fun ∘ step {C,γ = C,γ} f)
    Iso⟨ Σ-ap-iso₂ (λ f → pathToIso λ i → identity-f-r {k = in-fun ∘ out-fun {S = S}} in-inverse-out f i ≡ in-fun ∘ step {C,γ = C,γ} f) ⟩
  Σ (C -> 𝓛) (λ f → f ≡ in-fun ∘ step {C,γ = C,γ} f)
    Iso⟨ refl-iso ⟩
  Σ (C → 𝓛) (λ f → f ≡ Ψ {C,γ = C,γ} f)
    Iso⟨ sym-iso (Σ-ap-iso (sym-iso (lemma10-Iso {C,γ = C,γ})) (λ _ → refl-iso)) ⟩
  Σ (Cone C,γ) (λ c → e c ≡ Ψ {C,γ = C,γ} (e c))
    Iso⟨ Σ-ap-iso₂ (λ c → pathToIso λ i → e c ≡ funExt⁻ (commutivity {C,γ = C,γ}) c i) ⟩
  Σ (Cone C,γ) (λ c → e c ≡ e (Φ {C,γ = C,γ} c))
    Iso⟨ Σ-ap-iso₂ (λ c → pathToIso (e-inj {C,γ = C,γ})) ⟩
  Σ (Cone C,γ) (λ c → c ≡ Φ {C,γ = C,γ} c)
    Iso⟨ refl-iso ⟩
  Σ (Cone C,γ) (λ { (u , q) → (u , q) ≡ (ϕ₀ {C,γ = C,γ} u , ϕ₁ {C,γ = C,γ} u q)})
    Iso⟨ (Σ-ap-iso₂ λ {(u , q) → sym-iso (Σ-split-iso {a = u} {a' = ϕ₀ {C,γ = C,γ} u} {b = q} {b' = ϕ₁ {C,γ = C,γ} u q})}) ⟩
  Σ (Cone C,γ) (λ { (u , q) → Σ (u ≡ ϕ₀ {C,γ = C,γ} u) λ p → PathP (λ i → Cone₁ {C,γ = C,γ} (p i)) q (ϕ₁ {C,γ = C,γ} u q) })
    Iso⟨ (iso (λ {((u , p) , q , r) → (u , q) , p , r}) (λ {((u , q) , p , r) → (u , p) , (q , r)}) (λ _ → refl) λ _ → refl) ⟩
  Σ (Σ (Cone₀ {C,γ = C,γ}) (λ u → u ≡ ϕ₀ {C,γ = C,γ} u)) (λ { (u , p) → Σ (Cone₁ {C,γ = C,γ} u) λ q → PathP (λ i → Cone₁ {C,γ = C,γ} (p i)) q (ϕ₁ u q)})
    Iso⟨ sym-iso (Σ-ap-iso (pathToIso missing-0) λ x → pathToIso (missing-2 x)) ⟩
  Σ (Lift {ℓ-zero} {ℓ} Unit) (λ { (lift tt) → Lift {ℓ-zero} {ℓ} Unit })
    Iso⟨ (iso (λ x → lift tt) (λ _ → lift tt , lift tt) (λ b i → lift tt) (λ a i → lift tt , lift tt)) ⟩
  Lift {ℓ-zero} {ℓ} Unit ∎Iso

-- -- lim-coalg-iso
U-is-Unit : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ ⇒ M-coalg) ≡ Lift Unit
U-is-Unit {ℓ = ℓ} {S = S} C,γ@(C , γ) = isoToPath (U-is-Unit-Iso C,γ)

contr-is-ext : ∀ {ℓ} {A B : Set ℓ} -> A ≡ B -> isContr A ≡ isContr B
contr-is-ext p = λ i -> isContr (p i)

U-contr : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ∀ (x : U {C,γ = C,γ}) -> isContr (U {C,γ = C,γ})
U-contr {ℓ} {C,γ = C,γ} x =
  transport (sym (contr-is-ext {A = U {C,γ = C,γ}} (U-is-Unit C,γ)))
            (lift tt , λ { (lift tt) -> refl })

----------------------------------------------------
-- Finality properties for bisimulation relations --
----------------------------------------------------

M-final-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Final {S = S}
M-final-coalg {ℓ} {S = S} = M-coalg , λ C,γ → transport (sym (U-is-Unit C,γ)) (lift tt) , λ y → U-contr {C,γ = C,γ} y .snd y

final-coalg-property-2 : ∀ {ℓ} {S : Container {ℓ}} -> (C : Coalg₀ {S = S}) -> (F : Final {S = S}) -> ∀ (f g : C ⇒ F .fst) -> f ≡ g
final-coalg-property-2 C F f g = λ i -> compPath-filler (sym (F .snd C .snd f))  (F .snd C .snd g) i i -- follows from contractability

final-property : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> prod₁ sim ≡ prod₂  sim
final-property S R sim = final-coalg-property-2 {S = S} (R⁻-coalg sim) (M-final-coalg {S = S}) (prod₁ sim) (prod₂ sim)

final-property-2 : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> π₁ sim ≡ π₂  sim
final-property-2 S R sim = λ i -> final-property S R sim i .fst

bisimulation-property : ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ) -> (∀ {x} -> R x x) -> ((x : Σ (M S) (λ a → Σ (M S) (R a))) -> fst (snd x) ≡ fst x) -> bisimulation S M-coalg R
αᵣ (bisimulation-property S R R-refl _) = λ { ( a , b ) → fst (out-fun a) , λ x → (snd (out-fun a) x) , ((snd (out-fun a) x) , R-refl) }
rel₁ (bisimulation-property S R _ _) = funExt λ x → refl
rel₂ (bisimulation-property S R _ R-eq) = funExt λ x i → out-fun {S = S} (R-eq x i)

-------------------------------------------------------------
-- Coinduction principle for M-types (≈ Coinductive types) --
-------------------------------------------------------------

-- coinduction proof by: m ≡ π₁(m,m',r) ≡ π₂(m,m',r) ≡ m'
coinduction : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> ∀ {m m' : M S} -> R m m' -> m ≡ m'
coinduction {S = S} R sim {m} {m'} r = λ i -> funExt⁻ (final-property-2 S R sim) (m , (m' , r)) i

coinduction⁻ : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (∀ {x} -> R x x) ->  ∀ {m m' : M S} -> m ≡ m' -> R m m'
coinduction⁻ {S = S} R sim k {m} {m'} r = transport (cong (R m) r) k

postulate
  coinduction-iso1 : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (R-refl : ∀ {x} -> R x x) ->
                     ∀ {m} {m'} (p : m ≡ m') -> (coinduction R sim {m} {m'}) (coinduction⁻ R sim R-refl p) ≡ p

  coinduction-iso2 : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (R-refl : ∀ {x} -> R x x) ->
                     ∀ {m} {m'} (p : R m m') -> (coinduction⁻ R sim R-refl (coinduction R sim {m} {m'} p)) ≡ p

coinduction-is-equality : ∀ {ℓ} {S : Container {ℓ}} R ->
  (sim : bisimulation S M-coalg R) ->
  (R-refl : ∀ {x} -> R x x) ->
  R ≡ _≡_
coinduction-is-equality R sim R-refl i m m' =
  ua (isoToEquiv (iso
    (coinduction R sim {m} {m'})
    (coinduction⁻ R sim R-refl)
    (coinduction-iso1 R sim R-refl)
    (coinduction-iso2 R sim R-refl))) i

----------------
-- CoFixpoint --
----------------
