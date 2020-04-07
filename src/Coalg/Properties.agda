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

open import Cubical.Foundations.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path

open import helper

module Coalg.Properties where

open import Coalg.Base
open import Container
open import M

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

postulate
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

U-is-Unit-Iso :
  ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S})
  ------------------------------------
  → Iso (C,γ ⇒ M-coalg) (Lift Unit)
U-is-Unit-Iso {ℓ = ℓ} {S = S} C,γ@(C , γ) =
  let e = inv (lemma10-Iso {C,γ = C,γ}) in
  let 𝓛 = M S in
  U {C,γ = C,γ}
    Iso⟨ refl-iso ⟩
  Σ (C → 𝓛) (λ f → out-fun ∘ f ≡ step {C,γ = C,γ} f)
    Iso⟨ Σ-ap-iso₂ (λ f → pathToIso (sym in-inj)) ⟩
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
    Iso⟨ sym-iso (Σ-ap-iso (missing-0-Iso) λ x → (missing-2-Iso x)) ⟩
  Σ (Lift {ℓ-zero} {ℓ} Unit) (λ { (lift tt) → Lift {ℓ-zero} {ℓ} Unit })
    Iso⟨ (iso (λ x → lift tt) (λ _ → lift tt , lift tt) (λ b i → lift tt) (λ a i → lift tt , lift tt)) ⟩
  Lift {ℓ-zero} {ℓ} Unit ∎Iso

-- lim-coalg-iso
U-is-Unit : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ ⇒ M-coalg) ≡ Lift Unit
U-is-Unit {ℓ = ℓ} {S = S} C,γ@(C , γ) = isoToPath (U-is-Unit-Iso C,γ)

postulate
  naturality-1 : ∀ {ℓ} {A B : Set ℓ} (p : Iso A B) (x : A) → cong (fun p) (leftInv p x) ≡ rightInv p (fun p x)
  naturality-2 : ∀ {ℓ} {A B : Set ℓ} (p : Iso A B) (x : B) → cong (inv p) (rightInv p x) ≡ leftInv p (inv p x)

introduce-square :
  ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ∙ q ≡ (x ≡⟨ p ⟩ y ≡⟨ q ⟩ z ∎)
introduce-square {x = x} {y} {z} p q = p ∙ q ≡⟨ rUnit (p ∙ q) ⟩ (p ∙ q) ∙ refl  ≡⟨ sym (assoc p q refl) ⟩ (x ≡⟨ p ⟩ y ≡⟨ q ⟩ z ∎) ∎

square-helper :
  ∀ {ℓ} {A : Set ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) {h : z ≡ w} → (x ≡⟨ p ∙ q ⟩ h) ≡ (x ≡⟨ p ⟩ y ≡⟨ q ⟩ h)
square-helper {x = x} {y} {z} p q {h = h} = sym (assoc p q h)

-- isContr→isProp contr x y ≡ k

asdfasdf : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} → isContr ((x : A) → B x) → ((x : A) → isContr (B x))
asdfasdf contr x = contr .fst x , λ y → let temp = contr .snd λ x₁ → contr .fst x₁ in contr .fst x ≡⟨ {!!} ⟩ {!!}  ≡⟨ {!!} ⟩ y ∎

sdfa2-helper : ∀ {ℓ} {A : Set ℓ} → (contr : isContr A) → ((x : A) → isContr (x ≡ x))
sdfa2-helper {A = A} contr x =
  let temp : A ≡ Lift Unit
      temp = isoToPath (iso (λ _ → lift tt) (λ _ → contr .fst) refl-fun (contr .snd))
  in
  let temp'' : isContr ((x : A) → x ≡ x) ≡ isContr ((x : Lift Unit) → x ≡ x)
      temp'' = cong isContr (cong (λ k → (x : k) → x ≡ x) temp)
  in
    asdfasdf (transport (sym temp'') ((λ x₁ i → lift tt) , λ y i x₁ i₁ → lift tt)) x
    
sdfa2 : ∀ {ℓ} {A : Set ℓ} → (contr : isContr A) → ((x : A) → isContr (∀ y → x ≡ y))
sdfa2 {A = A} contr x = (isContr→isProp contr x), λ y →
  let temp'1 : isContr A
      temp'1 = x , y
  in
  let temp'2 : isContr A
      temp'2 = x , isContr→isProp contr x
  in
  let temp'3 : isProp (isContr A)
      temp'3 = isPropIsContr
  in
  let temp'4 : (x , y) ≡ (x , isContr→isProp contr x)
      temp'4 = temp'3 (x , y) (x , isContr→isProp contr x)
  in
  let temp'5 : _Σ≡T_ {B = λ a → (x : A) → a ≡ x} (x , y)  (x , isContr→isProp contr x)
      temp'5 = pathSigma→sigmaPath (x , y) (x , isContr→isProp contr x) temp'4
  in
  let temp'6 : PathP (λ i → (a : A) → y x i ≡ a) y (isContr→isProp contr x)
      temp'6 = transport (sym (PathP≡Path (λ i → (a : A) → y x i ≡ a ) y (isContr→isProp contr x))) (temp'5 .snd)
  in
  let temp'7 : (a : A) → PathP (λ i → y x i ≡ a) (y a) (isContr→isProp contr x a)
      temp'7 a i = temp'6 i a 
  in
  let temp'8 : (a : A) → (y x) ⁻¹ ∙' y a ≡ isContr→isProp contr x a
      temp'8 a = transport (PathP≡doubleCompPathˡ (y x) (y a) (isContr→isProp contr x a) (refl {x = a})) (temp'7 a)
  in
  let temp'9 : (a : A) → (y x) ⁻¹ ∙ y a ≡ isContr→isProp contr x a
      temp'9 a = transport (cong (λ k → k ≡ isContr→isProp contr x a) (sym (compPath≡compPath' (y x ⁻¹) (y a)))) (temp'8 a)
  in
  let temp'10 : (a : A) → (y x) ≡ refl
      temp'10 a = isContr→isProp (sdfa2-helper contr x) (y x) refl
  in
    funExt λ a →
    (isContr→isProp contr x a ≡⟨ sym (temp'9 a) ⟩ (y x) ⁻¹ ∙ y a  ≡⟨ cong (λ k → k ⁻¹ ∙ y a) (temp'10 a) ⟩ refl ⁻¹ ∙ y a  ≡⟨ cong (λ k → k ∙ y a) symRefl ⟩ refl ∙ y a ≡⟨ sym (lUnit (y a)) ⟩ y a ∎)

-- sdfa-helper : ∀ {A B} → isProp (∀ (y : A) → isContr (B y)) → (∀ (y : A) → isContr (B y))
-- sdfa-helper = {!!}

sdfa : ∀ {ℓ} {A : Set ℓ} → (x : isContr A) → ∀ y → isProp (x .fst ≡ y)
sdfa {A = A} x y = isContr→isProp (asdfasdf (sdfa2 x (x .fst)) y) -- sdfa2 ? ?


-- sdfa2 : ∀ {ℓ} {A : Set ℓ} → (x : isContr A) → ∀ y → isProp (Σ[ a ∈ (x ≡ (x .fst , y)) ] (∀ b → a ≡ b))
-- sdfa2 {A = A} x y =
--   let temp = isContr→isProp x in
--   isPropΣ (isContr→isProp {!!}) {!!} -- (isContr→isProp {!!})

abstract
  contr-is-ext-Iso-helper : ∀ {ℓ} {A B : Set ℓ} -> (p : Iso A B) -> ((a : A) → Iso (∀ y → a ≡ y) (∀ y → (fun p a) ≡ y))
  fun (contr-is-ext-Iso-helper (iso f g rightI leftI) a) = (λ x y → cong f (x (g y)) ∙ rightI y)
  inv (contr-is-ext-Iso-helper (iso f g rightI leftI) a) = (λ x y → sym (leftI a) ∙ cong g (x (f y)) ∙ leftI y)
  rightInv (contr-is-ext-Iso-helper p@(iso f g rightI leftI) a) = (λ b →  funExt λ y →
    sdfa (f a , b) y (cong f (sym (leftI a) ∙ cong g (b (f (g y))) ∙ leftI (g y)) ∙ rightI y) (b y)
  -- cong f ((sym (leftI a)) ∙ (cong g (b (f (g y)))) ∙ leftI (g y)) ∙ rightI y
  --   ≡⟨ introduce-square (cong f (sym (leftI a) ∙ cong g (b (f (g y))) ∙ leftI (g y))) (rightI y) ⟩
  -- (f a ≡⟨ cong f (sym (leftI a) ∙ cong g (b (f (g y))) ∙ leftI (g y)) ⟩ f (g y) ≡⟨ rightI y ⟩ y ∎)
  --   ≡⟨ cong (λ k → k ∙ rightI y ∙ refl) (cong-∙ f (sym (leftI a)) (cong g (b (f (g y))) ∙ leftI (g y))) ⟩
  -- (f a ≡⟨ cong f (sym (leftI a)) ∙ cong f (cong g (b (f (g y))) ∙ leftI (g y)) ⟩ f (g y) ≡⟨ rightI y ⟩ y ∎)
  --   ≡⟨ square-helper (cong f (sym (leftI a))) (cong f (cong g (b (f (g y))) ∙ leftI (g y))) ⟩
  -- (f a ≡⟨ cong f (sym (leftI a)) ⟩ f (g (f a)) ≡⟨ cong f (cong g (b (f (g y))) ∙ leftI (g y)) ⟩ f (g y) ≡⟨ rightI y ⟩ y ∎)
  --   ≡⟨ cong (λ k → cong f (sym (leftI a)) ∙ (cong f (cong g (b (f (g y))) ∙ k)) ∙ rightI y ∙ refl) (sym (naturality-2 p y)) ⟩
  -- (f a ≡⟨ cong f (sym (leftI a)) ⟩ f (g (f a)) ≡⟨ cong f (cong g (b (f (g y))) ∙ cong g (rightI y)) ⟩ f (g y) ≡⟨ rightI y ⟩ y ∎)
  --   ≡⟨ cong (λ k → cong f (sym (leftI a)) ∙ cong f k ∙ rightI y ∙ refl) (sym (cong-∙ g (b (f (g y))) (rightI y))) ⟩
  -- (f a ≡⟨ cong f (sym (leftI a)) ⟩ f (g (f a)) ≡⟨ cong f (cong g (b (f (g y)) ∙ rightI y)) ⟩ f (g y) ≡⟨ rightI y ⟩ y ∎)
  --   ≡⟨ cong (λ k → cong f (sym (leftI a)) ∙ cong f (cong g k) ∙ rightI y ∙ refl) (sdfa (f a , b) y (b (f (g y)) ∙ rightI y) (b y)) ⟩
  -- (f a ≡⟨ cong f (sym (leftI a)) ⟩ f (g (f a)) ≡⟨ cong f (cong g (b y)) ⟩ f (g y) ≡⟨ rightI y ⟩ y ∎)
  --   ≡⟨ sym (square-helper (cong f (sym (leftI a))) (cong f (cong g (b y)))) ⟩ 
  -- (f a ≡⟨ cong f (sym (leftI a)) ∙ cong f (cong g (b y)) ⟩ f (g y) ≡⟨ rightI y ⟩ y ∎)
  --   ≡⟨ cong (λ k → k ∙ rightI y ∙ refl) (sym (cong-∙ f (sym (leftI a)) (cong g (b y)))) ⟩
  -- (f a ≡⟨ cong f (sym (leftI a) ∙ cong g (b y)) ⟩ f (g y) ≡⟨ rightI y ⟩ y ∎)
  --   ≡⟨ cong (λ k → k ∙ rightI y ∙ refl) (sdfa (f a , b) (f (g y)) (cong f (sym (leftI a) ∙ cong g (b y))) (b (f (g y)))) ⟩
  -- (f a ≡⟨ b (f (g y)) ⟩ f (g y) ≡⟨ rightI y ⟩ y ∎)
  --   ≡⟨ sym (square-helper (b (f (g y))) (rightI y)) ⟩
  -- (f a ≡⟨ b (f (g y)) ∙ rightI y ⟩ y ∎)
  --   ≡⟨ cong (λ k → k ∙ refl) (sdfa (f a , b) y (b (f (g y)) ∙ rightI y) (b y)) ⟩
  -- (f a ≡⟨ b y ⟩ y ∎)
  --   ≡⟨ sym (rUnit (b y)) ⟩
  -- b y ∎
    )
  leftInv (contr-is-ext-Iso-helper p@(iso f g rightI leftI) a) = (λ b → funExt λ y →
    sdfa (a , b) y (sym (leftI a) ∙ cong g (cong f (b (g (f y))) ∙ rightI (f y)) ∙ leftI y) (b y)  
  -- sym (leftI a) ∙ cong g (cong f (b (g (f y))) ∙ rightI (f y)) ∙ leftI y
  --   ≡⟨ cong (λ k → sym (leftI a) ∙ cong g (cong f (b (g (f y))) ∙ k) ∙ leftI y) (sym (naturality-1 p y)) ⟩
  -- sym (leftI a) ∙ cong g (cong f (b (g (f y))) ∙ cong f (leftI y)) ∙ leftI y
  --   ≡⟨ cong (λ k → sym (leftI a) ∙ cong g k ∙ leftI y) (sym (cong-∙ f (b (g (f y))) (leftI y))) ⟩
  -- sym (leftI a) ∙ cong g (cong f (b (g (f y)) ∙ leftI y)) ∙ leftI y
  --   ≡⟨ cong (λ k → sym (leftI a) ∙ cong g (cong f k) ∙ leftI y) (sdfa (a , b) y (b (g (f y)) ∙ leftI y) (b y)) ⟩
  -- sym (leftI a) ∙ cong g (cong f (b y)) ∙ leftI y
  --   ≡⟨ assoc (sym (leftI a)) (cong g (cong f (b y))) (leftI y) ⟩
  -- (sym (leftI a) ∙ cong g (cong f (b y))) ∙ leftI y
  --   ≡⟨ cong (λ k → k ∙ leftI y) (sdfa (a , b) (g (f y)) (sym (leftI a) ∙ cong g (cong f (b y))) (b (g (f y)))) ⟩
  -- b (g (f y)) ∙ leftI y
  --   ≡⟨ sdfa (a , b) y (b (g (f y)) ∙ leftI y) (b y) ⟩
  -- b y ∎
    )
  
-- Can this be generalized to Iso A B → Iso (H A) (H B) , not just for H = isContr ?
contr-is-ext-Iso : ∀ {ℓ} {A B : Set ℓ} -> Iso A B -> Iso (isContr A) (isContr B) -- Σ[ x ∈ A ] (∀ y → x ≡ y)
contr-is-ext-Iso {A = A} {B} p = Σ-ap-iso p (contr-is-ext-Iso-helper p)

contr-is-ext : ∀ {ℓ} {A B : Set ℓ} -> A ≡ B -> isContr A ≡ isContr B
contr-is-ext = cong isContr

U-contr : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ∀ (x : U {C,γ = C,γ}) -> isContr (U {C,γ = C,γ})
U-contr {ℓ} {C,γ = C,γ} x =
  inv (contr-is-ext-Iso {A = U {C,γ = C,γ}} (U-is-Unit-Iso C,γ)) (lift tt , λ { (lift tt) -> refl })

-- U-contr : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ∀ (x : U {C,γ = C,γ}) -> isContr (U {C,γ = C,γ})
-- U-contr {ℓ} {C,γ = C,γ} x =
--   transport (sym (contr-is-ext {A = U {C,γ = C,γ}} (U-is-Unit C,γ)))
--             (lift tt , λ { (lift tt) -> refl })

----------------------------------------------------
-- Finality properties for bisimulation relations --
----------------------------------------------------

-- lim-terminal : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} → isContr (C,γ ⇒ M-coalg)
-- lim-terminal {C,γ = C,γ} = inv (U-is-Unit-Iso C,γ) (lift tt) , λ y → U-contr {C,γ = C,γ} y .snd y

-- coalg-unfold : ∀ {ℓ} {S : Container {ℓ}} -> (C,γ : Coalg₀ {S = S}) -> (_⇒_ {S = S} (C,γ) (M-coalg {S = S}))  -- unique function into final coalg
-- coalg-unfold C,γ = lim-terminal {C,γ = C,γ} .fst

-- coalg-unfold-universal : ∀ {ℓ} {S : Container {ℓ}} -> (C,γ : Coalg₀ {S = S}) -> (y : C,γ ⇒ M-coalg) → fst lim-terminal ≡ y  -- unique function into final coalg
-- coalg-unfold-universal C,γ = lim-terminal {C,γ = C,γ} .snd

-- coalg-unfold-function : ∀ {ℓ} {S : Container {ℓ}} -> (C,γ : Coalg₀ {S = S}) -> (C,γ .fst) -> (M-coalg .fst)  -- unique function into final coalg
-- coalg-unfold-function C,γ y = (coalg-unfold C,γ) .fst y

-- M-final-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Final {S = S}
-- M-final-coalg {ℓ} {S = S} = M-coalg , λ C,γ → lim-terminal {C,γ = C,γ}

-- -- final-is-contr : ∀ {ℓ} {S : Container {ℓ}} → isContr (Final {S = S})
-- -- final-is-contr = M-final-coalg , λ y → {!!}

-- final-coalg-property-2 : ∀ {ℓ} {S : Container {ℓ}} -> (C : Coalg₀ {S = S}) -> (F : Final {S = S}) -> ∀ (f g : C ⇒ F .fst) -> f ≡ g
-- final-coalg-property-2 C F f g = (sym (F .snd C .snd f)) ∙ (F .snd C .snd g) -- follows from contractability

-- final-property : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> prod₁ sim ≡ prod₂  sim
-- final-property S R sim = final-coalg-property-2 {S = S} (R⁻-coalg sim) (M-final-coalg {S = S}) (prod₁ sim) (prod₂ sim)

-- final-property-2 : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> π₁ sim ≡ π₂  sim
-- final-property-2 S R sim = cong fst (final-property S R sim)

-- bisimulation-property :
--   ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ)
--   → (∀ {x} -> R x x)
--   → ((x : Σ (M S) (λ a → Σ (M S) (R a))) → fst (snd x) ≡ fst x)
--   ------------------------------
--   → bisimulation S M-coalg R
-- αᵣ (bisimulation-property S R R-refl _) ( a , b ) = fst (out-fun a) , λ x → (snd (out-fun a) x) , ((snd (out-fun a) x) , R-refl)
-- rel₁ (bisimulation-property S R _ _) = funExt λ x → refl
-- rel₂ (bisimulation-property S R _ R-eq) = funExt λ x i → out-fun {S = S} (R-eq x i)

-- -------------------------------------------------------------
-- -- Coinduction principle for M-types (≈ Coinductive types) --
-- -------------------------------------------------------------

-- -- coinduction proof by: m ≡ π₁(m,m',r) ≡ π₂(m,m',r) ≡ m'
-- coinduction : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> ∀ {m m' : M S} -> R m m' -> m ≡ m'
-- coinduction {S = S} R sim {m} {m'} r = funExt⁻ (final-property-2 S R sim) (m , (m' , r))

-- coinduction⁻ : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (∀ {x} -> R x x) ->  ∀ {m m' : M S} -> m ≡ m' -> R m m'
-- coinduction⁻ {S = S} R sim k {m} {m'} r = subst (R m) r k
  
-- -- postulate
-- --   coinduction-iso1 :
-- --     ∀ {ℓ} {S : Container {ℓ}} R
-- --     → (sim : bisimulation S M-coalg R)
-- --     → (R-refl : ∀ {x} -> R x x) →
-- --     ∀ {m} {m'} (p : m ≡ m')
-- --     → (coinduction R sim {m} {m'}) (coinduction⁻ R sim R-refl p) ≡ p
    
-- -- postulate
-- --   coinduction-iso2 :
-- --     ∀ {ℓ} {S : Container {ℓ}} R
-- --     → (sim : bisimulation S M-coalg R)
-- --     → (R-refl : ∀ {x} -> R x x) →
-- --     ∀ {m} {m'} (p : R m m')
-- --     → (coinduction⁻ R sim R-refl (coinduction R sim {m} {m'} p)) ≡ p

-- -- coinduction-is-equality : ∀ {ℓ} {S : Container {ℓ}} R ->
-- --   (sim : bisimulation S M-coalg R) ->
-- --   (R-refl : ∀ {x} -> R x x) ->
-- --   R ≡ _≡_
-- -- coinduction-is-equality R sim R-refl =
-- --   funExt λ m →
-- --   funExt λ m' →
-- --     isoToPath (iso
-- --       (coinduction R sim {m} {m'})
-- --       (coinduction⁻ R sim R-refl)
-- --       (coinduction-iso1 R sim R-refl)
-- --       (coinduction-iso2 R sim R-refl))

-- -- ----------------
-- -- -- CoFixpoint --
-- -- ----------------
