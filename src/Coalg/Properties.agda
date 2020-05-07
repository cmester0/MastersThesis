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
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path

open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv

open import Cubical.Codata.M.AsLimit.helper

open import Cubical.Codata.M.AsLimit.Coalg.Base
open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M

module Coalg.Properties where

open Iso

-----------------------------------------------------------------------------
-- The limit of a Polynomial functor over a Container is a Final Coalgebra --
-----------------------------------------------------------------------------

Ps : ∀ {ℓ} -> (S : Container {ℓ}) -> (C,γ : Coalg₀ {S = S}) -> Container {ℓ}
Ps S T = T .fst , λ x → P₀ {S = S}  (T .fst)

Ms : ∀ {ℓ} -> (S : Container {ℓ}) -> Container {ℓ}
Ms S = M S , λ x → P₀ {S = S}  (M S)

M-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S}
M-coalg {S = S} =
  (M S) , out-fun

PM-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Coalg₀ {S = S}
PM-coalg {S = S} =
  (P₀ (M S)) , P₁ out-fun

Final : ∀ {ℓ} {S : Container {ℓ}} -> Set (ℓ-suc ℓ)
Final {S = S} = Σ (Coalg₀ {S = S}) λ X,ρ → ∀ (C,γ : Coalg₀ {S = S}) -> isContr (_⇒_ {S = S} (C,γ) (X,ρ))

--------------------------------------------------------
-- Properties of Bisimulations and (Final) Coalgebras --
--------------------------------------------------------

U : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Set ℓ
U {S = S} {C,γ = C,γ} =
  Σ (C,γ .fst -> M S) λ f → out-fun ∘ f ≡ P₁ f ∘ C,γ .snd

open Iso

step : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} {Y : Set ℓ} (f : C,γ .fst -> Y) → C,γ .fst → P₀ Y
step {C,γ = C,γ} {Y = Y} f = P₁ f  ∘ C,γ .snd

Ψ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} (f : C,γ .fst -> M S) -> C,γ .fst -> M S
Ψ {S = S} {C,γ = C,γ} f =
  in-fun ∘ step {C,γ = C,γ} f

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

-- commutivity : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}}
--   → let e = inv (lemma10-Iso {C,γ = C,γ}) in
--   ∀ (c : Cone C,γ) → Ψ {C,γ = C,γ} (e c) ≡ e (Φ {C,γ = C,γ} c)
-- commutivity {C,γ = C,γ} (c₀ , c₁) =
--   let e = inv (lemma10-Iso {C,γ = C,γ}) in
--   sym (leftInv (lemma10-Iso {C,γ = C,γ}) (Ψ {C,γ = C,γ} (e (c₀ , c₁)))) ∙
--   cong (inv (lemma10-Iso {C,γ = C,γ}))
--        (ΣPathP (funExt₂ (λ n z → {!!}) , {!!}) ∙ cong Φ (rightInv (lemma10-Iso {C,γ = C,γ}) (c₀ , c₁)))

postulate -- Naturality
  commutivity : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}}
    → let e = inv (lemma10-Iso {C,γ = C,γ}) in
    Ψ {C,γ = C,γ} ∘ e ≡ e ∘ Φ {C,γ = C,γ}

e-inj-Iso : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} {x y}
  → Iso (inv (lemma10-Iso {C,γ = C,γ}) x ≡ inv (lemma10-Iso {C,γ = C,γ}) y)
         (x ≡ y)
e-inj-Iso {C,γ = C,γ} = ≡-rel-b-inj-x-Iso (lemma10-Iso {C,γ = C,γ})

e-inj : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} {x y}
  → (inv (lemma10-Iso {C,γ = C,γ}) x ≡ inv (lemma10-Iso {C,γ = C,γ}) y)
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

missing-0-Iso : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Iso (Lift {ℓ-zero} {ℓ} Unit) (Σ (Cone₀ {C,γ = C,γ}) (λ u → u ≡ ϕ₀ {C,γ = C,γ} u))
fun (missing-0-Iso {S = S}) = (λ _ → u0 , (funExt p0))   
inv (missing-0-Iso {S = S}) = (λ x → lift tt)
rightInv (missing-0-Iso {S = S}) = (λ b → missing-0-helper b)
leftInv (missing-0-Iso {S = S}) = λ a i → lift tt

-- missing-0 : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Lift Unit ≡ Σ (Cone₀ {C,γ = C,γ}) (λ u → u ≡ ϕ₀ {C,γ = C,γ} u)
-- missing-0 {S = S} = isoToPath missing-0-Iso

postulate
  missing-2-Iso : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ((x : Lift Unit) → Iso (Lift {ℓ-zero} {ℓ} Unit) (Σ (Cone₁ {C,γ = C,γ} ((fun (missing-0-Iso {C,γ = C,γ}) x) .fst)) (λ q → PathP (λ i → Cone₁ {C,γ = C,γ} ((fun (missing-0-Iso {C,γ = C,γ}) x) .snd i)) q (ϕ₁ {C,γ = C,γ} ((fun (missing-0-Iso {C,γ = C,γ}) x) .fst) q))))

  missing-2 : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ((x : Lift Unit) → Lift {ℓ-zero} {ℓ} Unit ≡ (Σ (Cone₁ {C,γ = C,γ} ((fun (missing-0-Iso {C,γ = C,γ}) x) .fst)) (λ q → PathP (λ i → Cone₁ {C,γ = C,γ} ((fun (missing-0-Iso {C,γ = C,γ}) x) .snd i)) q (ϕ₁ {C,γ = C,γ} ((fun (missing-0-Iso {C,γ = C,γ}) x) .fst) q))))

computation-abstract'0 : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} {f g : C,γ .fst → P₀ (M S)} → Iso (in-fun ∘ f ≡ in-fun ∘ g) (f ≡ g)
computation-abstract'0 {ℓ} {S} {C,γ} {f} {g} = temp
  where
    abstract
      temp : Iso (in-fun ∘ f ≡ in-fun ∘ g) (f ≡ g)
      temp = ≡-rel-a-inj-Iso {ℓ = ℓ} {A = P₀ (M S)} {B = M S} {C = C,γ .fst} (shift-iso {S = S}) {f = f} {g = g}

computation-abstract'1 : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} (f : C,γ .fst → M S) → in-fun ∘ out-fun ∘ f ≡ f
computation-abstract'1 {S = S} = temp
  where
    abstract
      temp : ∀ f → in-fun ∘ out-fun ∘ f ≡ f
      temp = identity-f-r {k = in-fun ∘ out-fun {S = S}} (in-inverse-out {S = S})

U-is-Unit-Iso :
  ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S})
  ------------------------------------
  → Iso {ℓ = ℓ} {ℓ' = ℓ} (C,γ ⇒ M-coalg) (Lift Unit)
U-is-Unit-Iso {ℓ = ℓ} {S = S} C,γ@(C , γ) =
  let e = inv (lemma10-Iso {C,γ = C,γ}) in
  let 𝓛 = M S in
    U {C,γ = C,γ}  
      Iso⟨ refl-iso ⟩
    Σ (C → 𝓛) (λ f → out-fun ∘ f ≡ step {C,γ = C,γ} f)
      Iso⟨ Σ-ap-iso₂ (λ f → sym-iso (computation-abstract'0 {C,γ = C,γ} {f = out-fun ∘ f} {g = step {C,γ = C,γ} f})) ⟩
    Σ (C → 𝓛) (λ f → in-fun ∘ out-fun ∘ f ≡ in-fun ∘ step {C,γ = C,γ} f)
      Iso⟨ Σ-ap-iso₂ (λ f → pathToIso (cong (λ k → k ≡ in-fun ∘ step {C,γ = C,γ} f) (computation-abstract'1 {C,γ = C,γ} f))) ⟩
    Σ (C -> 𝓛) (λ f → f ≡ in-fun ∘ step {C,γ = C,γ} f)
      Iso⟨ refl-iso ⟩
    Σ (C → 𝓛) (λ f → f ≡ Ψ {C,γ = C,γ} f)
      Iso⟨ sym-iso (Σ-ap-iso (sym-iso (lemma10-Iso {C,γ = C,γ})) (λ _ → refl-iso)) ⟩
    Σ (Cone C,γ) (λ c → e c ≡ Ψ {C,γ = C,γ} (e c))
      Iso⟨ Σ-ap-iso₂ (λ c → pathToIso λ i → e c ≡ funExt⁻ (commutivity {C,γ = C,γ}) c i) ⟩
    Σ (Cone C,γ) (λ c → e c ≡ e (Φ {C,γ = C,γ} c))
      Iso⟨ Σ-ap-iso₂ (λ c → e-inj-Iso {C,γ = C,γ}) ⟩
    Σ (Cone C,γ) (λ c → c ≡ Φ {C,γ = C,γ} c)
      Iso⟨ refl-iso ⟩
    Σ (Cone C,γ) (λ { (u , q) → (u , q) ≡ (ϕ₀ {C,γ = C,γ} u , ϕ₁ {C,γ = C,γ} u q)})
      Iso⟨ (Σ-ap-iso₂ λ {(u , q) → sym-iso (Σ-split-iso {a = u} {a' = ϕ₀ {C,γ = C,γ} u} {b = q} {b' = ϕ₁ {C,γ = C,γ} u q})}) ⟩
    Σ (Cone C,γ) (λ { (u , q) → Σ (u ≡ ϕ₀ {C,γ = C,γ} u) λ p → PathP (λ i → Cone₁ {C,γ = C,γ} (p i)) q (ϕ₁ {C,γ = C,γ} u q) })
      Iso⟨ (iso (λ {((u , p) , q , r) → (u , q) , p , r}) (λ {((u , q) , p , r) → (u , p) , (q , r)}) (λ _ → refl) λ _ → refl) ⟩
    Σ (Σ (Cone₀ {C,γ = C,γ}) (λ u → u ≡ ϕ₀ {C,γ = C,γ} u)) (λ { (u , p) → Σ (Cone₁ {C,γ = C,γ} u) λ q → PathP (λ i → Cone₁ {C,γ = C,γ} (p i)) q (ϕ₁ u q)})
      Iso⟨ sym-iso (Σ-ap-iso (missing-0-Iso) λ x → (missing-2-Iso x)) ⟩
    Σ (Lift {ℓ-zero} {ℓ} Unit) (λ { (lift tt) → Lift {ℓ-zero} {ℓ} Unit })
      Iso⟨ (iso (λ x → lift tt) (λ _ → lift tt , lift tt) (λ b i → lift tt) (λ a i → lift tt , lift tt)) ⟩
    Lift {ℓ-zero} {ℓ} Unit ∎Iso

isContrIsPropPath : ∀ {ℓ} {A : Set ℓ} → (x : isContr A) → ∀ y → isProp (x .fst ≡ y)
isContrIsPropPath {A = A} x y = isContr→isProp (isContr→isContrPath x (x .fst) y)

contr-is-ext-Iso-helper : ∀ {ℓ} {A B : Set ℓ} -> (p : Iso A B) -> ((a : A) → Iso (∀ y → a ≡ y) (∀ y → (fun p a) ≡ y))
fun (contr-is-ext-Iso-helper (iso f g rightI leftI) a) x y = cong f (x (g y)) ∙ rightI y
inv (contr-is-ext-Iso-helper (iso f g rightI leftI) a) x y = sym (leftI a) ∙ cong g (x (f y)) ∙ leftI y
rightInv (contr-is-ext-Iso-helper p@(iso f g rightI leftI) a) b = funExt λ y → isContrIsPropPath (f a , b) y (cong f (sym (leftI a) ∙ cong g (b (f (g y))) ∙ leftI (g y)) ∙ rightI y) (b y)
leftInv (contr-is-ext-Iso-helper p@(iso f g rightI leftI) a) b = funExt λ y → isContrIsPropPath (a , b) y (sym (leftI a) ∙ cong g (cong f (b (g (f y))) ∙ rightI (f y)) ∙ leftI y) (b y)
  
-- Can this be generalized to Iso A B → Iso (H A) (H B) , not just for H = isContr ?
contr-is-ext-Iso : ∀ {ℓ} {A B : Set ℓ} -> Iso A B -> Iso (isContr A) (isContr B) -- Σ[ x ∈ A ] (∀ y → x ≡ y)
contr-is-ext-Iso {A = A} {B} p = Σ-ap-iso p (contr-is-ext-Iso-helper p)

contr-is-ext : ∀ {ℓ} {A B : Set ℓ} -> A ≡ B -> isContr A ≡ isContr B
contr-is-ext = cong isContr

U-contr : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> isContr (U {C,γ = C,γ})
U-contr {ℓ} {C,γ = C,γ} = inv (contr-is-ext-Iso {A = U {C,γ = C,γ}} (U-is-Unit-Iso C,γ)) (lift tt , λ { (lift tt) -> refl })

----------------------------------------------------
-- Finality properties for bisimulation relations --
----------------------------------------------------

lim-terminal : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} → isContr (C,γ ⇒ M-coalg)
lim-terminal {C,γ = C,γ} = inv (U-is-Unit-Iso C,γ) (lift tt) , U-contr {C,γ = C,γ} .snd

coalg-unfold : ∀ {ℓ} {S : Container {ℓ}} -> (C,γ : Coalg₀ {S = S}) -> (_⇒_ {S = S} (C,γ) (M-coalg {S = S}))  -- unique function into final coalg
coalg-unfold C,γ = lim-terminal {C,γ = C,γ} .fst

coalg-unfold-universal : ∀ {ℓ} {S : Container {ℓ}} -> (C,γ : Coalg₀ {S = S}) -> (y : C,γ ⇒ M-coalg) → fst lim-terminal ≡ y  -- unique function into final coalg
coalg-unfold-universal C,γ = lim-terminal {C,γ = C,γ} .snd

coalg-unfold-function : ∀ {ℓ} {S : Container {ℓ}} -> (C,γ : Coalg₀ {S = S}) -> (C,γ .fst) -> (M-coalg .fst)  -- unique function into final coalg
coalg-unfold-function C,γ y = (coalg-unfold C,γ) .fst y

M-final-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Final {S = S}
M-final-coalg {ℓ} {S = S} = M-coalg , λ C,γ → lim-terminal {C,γ = C,γ}

-- final-is-contr : ∀ {ℓ} {S : Container {ℓ}} → isContr (Final {S = S})
-- final-is-contr = M-final-coalg , λ y → {!!}

final-coalg-property-2 : ∀ {ℓ} {S : Container {ℓ}} -> (C : Coalg₀ {S = S}) -> (F : Final {S = S}) -> ∀ (f g : C ⇒ F .fst) -> f ≡ g
final-coalg-property-2 C F f g = (sym (F .snd C .snd f)) ∙ (F .snd C .snd g) -- follows from contractability
