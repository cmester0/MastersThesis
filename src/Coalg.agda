{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-} --safe

open import M

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( _∘_ )

open import Cubical.Data.Unit

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Id using (ap ; _∙_)
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import helper

open import Cubical.Data.Sigma

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

postulate
  equality-relation-projection : ∀ {A R} (eq : equality-relation R) -> (x : Σ A (λ a → Σ A (R a))) -> (fst x) ≡ (fst (x .snd))
  equality-mono : ∀ {A R} (eq : equality-relation R) (f : A -> A) (x y : A) -> R x y → R (f x) (f y)
  equality-relation-projection-2 : ∀ {S R} (eq : equality-relation R) -> (x : Σ (M S) (λ a → Σ (M S) (R a))) -> (fst x) ≡ (fst (x .snd))

--------------------------------------------------------
-- Properties of Bisimulations and (Final) Coalgebras --
--------------------------------------------------------

unfold : ∀ {ℓ} {S : Container {ℓ}} -> (X,ρ : Final {S = S}) -> (C,γ : Coalg₀ {S = S}) -> (_⇒_ {S = S} (C,γ) (X,ρ .fst))  -- unique function into final coalg
unfold X,ρ C,γ = X,ρ .snd C,γ .fst

unfold-function : ∀ {ℓ} {S : Container {ℓ}} -> (X,ρ : Final {S = S}) -> (C,γ : Coalg₀ {S = S}) -> (C,γ .fst) -> (X,ρ .fst .fst)  -- unique function into final coalg
unfold-function X,ρ C,γ y = (unfold X,ρ C,γ) .fst y

U : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Set ℓ
U {S = S} {C,γ = C,γ} = Σ (C,γ .fst -> M S) λ f → out-fun ∘ f ≡ P₁ f ∘ C,γ .snd

U-to-Unit : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> U {C,γ = C,γ} -> Lift {ℓ-zero} {ℓ} Unit
U-to-Unit _ = lift tt

open Chain

Cone : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> Set ℓ
Cone {S = S} (C , θ) = Σ ((n : ℕ) → C → X (sequence S) n) λ f → (n : ℕ) → π (sequence S) ∘ (f (suc n)) ≡ f n

projection : ∀ {ℓ} {S : Container {ℓ}} n -> M S -> X (sequence S) n
projection n (x , q) = x n

β : ∀ {ℓ} {S : Container {ℓ}} -> (n : ℕ) → ∀ x → π (sequence S) {n = n} (projection (suc n) x) ≡ projection n x
β n (x , q) = q n
             
lemma10' : ∀ {ℓ} {S : Container {ℓ}} -> (Σ ((n : ℕ) → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) (u (suc n)) ≡ u n) ≡ M S
lemma10' = isoToPath (iso (λ { (u , q) → (λ n → u n) , λ n → q n} ) (λ f → (λ n → projection n f) , λ n → β n f) (λ { (u , q) → refl}) λ f → refl)

unapΣ : ∀ {i j}{A : Set i}{B : A → Set j}
          {a a' : A} {b : B a} {b' : B a'}
        → (Σ (a ≡ a') λ q → PathP (λ i → B (q i)) b b')
        → (a , b) ≡ (a' , b')
unapΣ x = ΣPathP (x .fst , x .snd)

subst-naturality : ∀ {i i' j} {X : Set i} {Y : Set i'}
                   {x x' : X} (P : Y → Set j)
                   (f : X → Y) (p : x ≡ x') (u : P (f x))
                 → subst (P ∘ f) p u ≡ subst P (λ i -> f (p i)) u
subst-naturality _ _ _ _ = refl

    
coherent : ∀ {i} {X Y : Set i} → X ≡ Y → Set i
coherent {X = X} f = ∀ (x : X) → cong (to {f = f}) (iso₁ {f = f} x) ≡  iso₂ {f = f} (to {f = f} x)
  where
    to : ∀ {i} {X Y : Set i} {f : X ≡ Y} -> X → Y
    to {f = f} = transport f

    from : ∀ {i} {X Y : Set i}  {f : X ≡ Y} -> Y → X
    from  {f = f} = transport⁻ f

    iso₁ : ∀ {i} {X Y : Set i} {f : X ≡ Y} -> (x : X) → from {f = f} (to {f = f} x) ≡ x
    iso₁ {f = f} = transport⁻Transport f

    iso₂ : ∀ {i} {X Y : Set i} {f : X ≡ Y} -> (y : Y) → to {f = f} (from {f = f} y) ≡ y
    iso₂ {f = f} = transportTransport⁻ f


-- coherent isomorphisms
_≅'_ : ∀ {i} → (X Y : Set i) → Set _
X ≅' Y = Σ (X ≡ Y) coherent

asdf : ∀ {ℓ} {X Y : Set ℓ} {f : X ≡ Y} -> coherent {X = X} {Y = Y} (isoToPath (iso (transport f) (transport⁻ f) (transportTransport⁻ f) (transport⁻Transport f)))
asdf = λ x i → {!!}

subst-hom : ∀ {i j} {X : Set i} (P : X → Set j) {x y z : X}
          → (p : x ≡ y) (q : y ≡ z) (u : P x)
          → subst P q (subst P p u) ≡ subst P (p □ q) u
subst-hom P p q u = sym (substComposite-□ P p q u)

Σ-ap-iso₁ : ∀ {i j} {X X' : Set i} {Y : X' → Set j}
          → (isom : X ≡ X')
          → Σ X (Y ∘ transport isom) ≡ Σ X' Y
Σ-ap-iso₁ {i} {j }{X} {X'} {Y} isom =
  let
    f : X → X'
    f = transport {A = X} {B = X'} isom

    g : X' → X
    g = transport⁻ {A = X} {B = X'} isom
               
    K : ∀ a → f (g a) ≡ a
    K a = transportTransport⁻ {A = X} {B = X'} isom a
               
    H : ∀ b → g (f b) ≡ b
    H b = transport⁻Transport {A = X} {B = X'} isom b  
  in
    isoToPath (iso (λ {(x , y) → f x , y})
                   (λ {(x , y) → g x , subst Y (sym (K x)) y})
                   (λ {(x , y) → ΣPathP (K x , {!!} )}) -- (subst-hom {!!} (sym (K x)) (K x) {!!}) □ (λ j → (λ p → subst Y p y) (rCancel (K x) j))
                   (λ {(x , y) → ΣPathP (H x , {!!})}))
               
Σ-ap-iso₂ : ∀ {i j} {X : Set i}
          → {Y : X → Set j}{Y' : X → Set j}
          → ((x : X) → Y x ≡ Y' x)
          → Σ X Y ≡ Σ X Y'
Σ-ap-iso₂ {X = X} {Y} {Y'} isom =
  isoToPath (iso (λ { (x , y) → x , transport (isom x) y})
                      (λ { (x , y') → x , transport (sym (isom x)) y'})
                      (λ { (x , y) →  ΣPathP (refl , transportTransport⁻ (isom x) y)})
                      (λ { (x , y') → ΣPathP (refl , transport⁻Transport (isom x) y')}))

Σ-ap-iso : ∀ {i j} {X X' : Set i}
           {Y : X → Set j} {Y' : X' → Set j}
         → (isom : X ≡ X')
         → ((x : X) → Y x ≡ Y' (transport isom x))
         → Σ X Y ≡ Σ X' Y'
Σ-ap-iso {X = X} {X'} {Y} {Y'} isom isom' = (Σ-ap-iso₂ isom') □ Σ-ap-iso₁ isom

-- -- Σ ((n : ℕ) → C -> X (sequence S) n) λ u → (n : ℕ) → π (sequence S)  (u (suc n)) ≡ u n
-- -- Σ ((n : ℕ) → C → X (sequence S) n) λ f → (n : ℕ) → π (sequence S) ∘ (f (suc n)) ≡ f n

lemma10 : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ .fst -> M S) ≡ Cone C,γ
lemma10 {S = S} C,γ@(C , γ) =
  isoToPath (iso (λ {f → (λ n z → projection n (f z)) , λ n i a → β n (f a) i})
                 (λ {(u , q) z → (λ n → u n z) , (λ n i → q n i z)})
                 (λ _ → refl)
                  λ _ → refl)

-- FunctionToProjection : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀) -> Cone C,γ -> C,γ .fst -> M S
-- FunctionToProjection {S = S} C,γ c = transp (λ i → sym (lemma10 C,γ) i) i0 c

-- step : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} {Y : Set ℓ} (f : C,γ .fst -> Y) → C,γ .fst → P₀ Y
-- step {C,γ = C,γ} {Y = Y} f = P₁ f  ∘ C,γ .snd

-- Ψ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} (f : C,γ .fst -> M S) -> C,γ .fst -> M S
-- Ψ {C,γ = C,γ} f = in-fun ∘ step {C,γ = C,γ} f

-- ϕ₀ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} (u : (n : ℕ) → C,γ .fst → X (sequence S) n) -> (n : ℕ) -> C,γ .fst -> W S n
-- ϕ₀ u 0 = λ x -> lift tt
-- ϕ₀ {C,γ = C,γ} u (suc n) = step {C,γ = C,γ} (u n)
           
-- ϕ₁ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}}
--            (u : (n : ℕ) → C,γ .fst → X (sequence S) n) ->
--            (g : (n : ℕ) → π (sequence S) ∘ u (suc n) ≡ u n) ->
--            (n : ℕ) → π (sequence S) ∘ (ϕ₀ {C,γ = C,γ} u (suc n)) ≡ ϕ₀ {C,γ = C,γ} u n
-- ϕ₁ u g 0 i = !
-- ϕ₁ {S = S} {C,γ = C,γ'} u g (suc n) = λ i a → step {C,γ = C,γ'} (λ x → g n i x) a

-- Φ : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Cone C,γ -> Cone C,γ
-- Φ {S = S} {C,γ = C,γ} (u , g) = ϕ₀ {C,γ = C,γ} u , ϕ₁ {S = S} {C,γ = C,γ} u g
      
-- postulate
--   commutivity : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> let e = FunctionToProjection C,γ in Ψ {C,γ = C,γ} ∘ e ≡ e ∘ Φ {C,γ = C,γ}

-- postulate
--   e-inj : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} x y -> (FunctionToProjection C,γ x ≡ FunctionToProjection C,γ y) ≡ (x ≡ y)

-- U-is-Unit : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ ⇒ M-coalg) ≡ Lift Unit
-- U-is-Unit {ℓ = ℓ} {S = S} C,γ@(C , γ) =
--   let e = FunctionToProjection C,γ in
--   let 𝓛 = M S in
--     U {C,γ = C,γ}
--   ≡⟨ refl ⟩
--     Σ (C → 𝓛) (λ f → out-fun ∘ f ≡ step {C,γ = C,γ} f)
--   ≡⟨ (λ i → Σ (C → 𝓛) (λ f → in-inj {f = out-fun ∘ f} {g = step {C,γ = C,γ} f} (~ i))) ⟩ 
--     Σ (C → 𝓛) (λ f → in-fun ∘ out-fun ∘ f ≡ in-fun ∘ step {C,γ = C,γ} f)
--   ≡⟨ (λ i → Σ (C,γ .fst → M S) (λ f → identity-f-r {k = in-fun ∘ out-fun {S = S}} in-inverse-out f i ≡ in-fun ∘ step {C,γ = C,γ} f)) ⟩ 
--     Σ (C -> 𝓛) (λ f → f ≡ in-fun ∘ step {C,γ = C,γ} f)
--   ≡⟨ refl ⟩
--     Σ (C → 𝓛) (λ f → f ≡ Ψ {C,γ = C,γ} f)
--   ≡⟨ {!!} ⟩
--     Σ (Cone C,γ) (λ c → e c ≡ Ψ {C,γ = C,γ} (e c))
--   ≡⟨ (λ i → Σ (Cone C,γ) (λ c → e c ≡ funExt⁻ (commutivity {C,γ = C,γ}) c i)) ⟩
--     Σ (Cone C,γ) (λ c → e c ≡ e (Φ {C,γ = C,γ} c))
--   ≡⟨ (λ i → Σ (Cone C,γ) (λ c → e-inj {C,γ = C,γ} c (Φ {C,γ = C,γ} c) i)) ⟩
--     Σ (Cone C,γ) (λ c → c ≡ Φ {C,γ = C,γ} c)
--   ≡⟨ {!!} ⟩
--     Σ (Cone C,γ) (λ { (u , q) → Σ (u ≡ ϕ₀ {C,γ = C,γ} u) λ p → (λ n → transport (λ i → (λ x → π (sequence S) (p i (suc n) x)) ≡ p i n) (q n)) ≡ ϕ₁ {C,γ = C,γ} u q })
--   ≡⟨ {!!} ⟩
--     Σ ((n : ℕ) → C → X (sequence S) n) (λ u → Σ (u ≡ ϕ₀ {C,γ = C,γ} u) λ p → Σ ((n : ℕ) → π (sequence S) ∘ u (suc n) ≡ u n) λ q → (λ n → transport (λ i → (λ x → π (sequence S) (p i (suc n) x)) ≡ p i n) (q n)) ≡ ϕ₁ u q)
--   ≡⟨ {!!} ⟩
--     (Σ (Lift {ℓ-zero} {ℓ} Unit) (λ { (lift tt) → Lift {ℓ-zero} {ℓ} Unit }))
--   ≡⟨ {!!} ⟩
--     Lift Unit ∎

-- -- contr-is-ext : ∀ {ℓ} {A B : Set ℓ} -> A ≡ B -> isContr A ≡ isContr B
-- -- contr-is-ext p = λ i -> isContr (p i)
  
-- -- U-contr : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> ∀ (x : U {C,γ = C,γ}) -> isContr (U {C,γ = C,γ})
-- -- U-contr {ℓ} {C,γ = C,γ} x = transp (λ i -> (sym (contr-is-ext {A = U {C,γ = C,γ}} U-is-Unit)) i) i0 (lift tt , λ { (lift tt) -> refl })

-- -- ----------------------------------------------------
-- -- -- Finality properties for bisimulation relations --
-- -- ----------------------------------------------------

-- -- M-final-coalg : ∀ {ℓ} {S : Container {ℓ}} -> Final {S = S}
-- -- M-final-coalg {ℓ} {S = S} = M-coalg , λ C,γ → transport (sym (U-is-Unit {C,γ = C,γ})) (lift tt) , λ y → U-contr {C,γ = C,γ} y .snd y

-- -- -- final-coalg-property-2 : ∀ {ℓ} {S : Container {ℓ}} -> (C : Coalg₀ {S = S}) -> (F : Final {S = S}) -> ∀ (f g : C ⇒ F .fst) -> f ≡ g
-- -- -- final-coalg-property-2 C F f g = λ i -> compPath-filler (sym (F .snd C .snd f))  (F .snd C .snd g) i i -- follows from contractability

-- -- -- final-property : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> prod₁ sim ≡ prod₂  sim
-- -- -- final-property S R sim = final-coalg-property-2 {S = S} (R⁻-coalg sim) (M-final-coalg {S = S}) (prod₁ sim) (prod₂ sim)

-- -- -- final-property-2 : ∀ {ℓ} (S : Container {ℓ}) R -> (sim : bisimulation S M-coalg R) -> π₁ sim ≡ π₂  sim
-- -- -- final-property-2 S R sim = λ i -> final-property S R sim i .fst

-- -- -- -- property : ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ) -> (∀ {x} -> R x x) -> (∀ (x : Σ (M S) (λ a → Σ (M S) (R a))) -> (fst (x .snd)) ≡ (fst x)) -> bisimulation S M-coalg R
-- -- -- -- αᵣ (property S R R-refl R-property) = λ { ( a , b ) → fst (out-fun a) , λ x → (snd (out-fun a) x) , ((snd (out-fun a) x) , R-refl) }
-- -- -- -- rel₁ (property S R R-refl R-property) = funExt λ x → refl
-- -- -- -- rel₂ (property S R R-refl R-property) = funExt λ x i → out-fun (R-property x i)

-- -- -- -- property-2 : ∀ {ℓ} {S : Container {ℓ}} (R : M S -> M S -> Set ℓ) -> (R-refl : ∀ {x} -> R x x) ->
-- -- -- --   (Σ (M S) (λ a → Σ (M S) (R a)) ,
-- -- -- --   (λ { (a , b) → fst (out-fun {S = S} a) , (λ x → snd (out-fun a) x , snd (out-fun a) x , R-refl) }))
-- -- -- --     ⇒
-- -- -- --   M-coalg {S = S}
-- -- -- -- property-2 {S = S} R R-refl = unfold M-final-coalg (Σ (M S) (λ a → Σ (M S) (R a)) , λ { (a , b)
-- -- -- --                                                                                             → fst (out-fun {S = S} a) ,
-- -- -- --                                                                                               (λ x → snd (out-fun a) x , snd (out-fun a) x , R-refl)
-- -- -- --                                                                                         })

-- -- -- -- λ C,γ → λ y → U-contr {C,γ = C,γ} y .snd y

-- -- -- -- property-3 : ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ) -> (∀ {x} -> R x x) -> (x : Σ (M S) (λ a → Σ (M S) (R a))) -> fst (snd x) ≡ fst x
-- -- -- -- property-3 S R R-refl x i =
-- -- -- --   let y = property-2 {S = S} R R-refl in -- (property-2 {S = S} R R-refl)
-- -- -- --   (U-contr
-- -- -- --     {C,γ = Σ (M S) (λ a → Σ (M S) (R a)) ,
-- -- -- --              λ { (a , b)
-- -- -- --                    → fst (out-fun {S = S} a) ,
-- -- -- --                      λ x →
-- -- -- --                        (snd (out-fun {S = S} a) x) ,
-- -- -- --                        ((snd (out-fun {S = S} a) x) , R-refl)
-- -- -- --                }} -- (Σ (M S) (λ a → Σ (M S) (R a)) , λ { (a , b) → fst (out-fun {S = S} a) , λ x → (snd (out-fun {S = S} a) x) , ((snd (out-fun {S = S} a) x) , R-refl)})
-- -- -- --     y .snd y {!!} .fst x)

-- -- -- -- property-3 : ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ) -> (∀ {x} -> R x x) -> (x : Σ (M S) (λ a → Σ (M S) (R a))) -> fst (snd x) ≡ fst x
-- -- -- -- property-3 S R R-refl x i =
-- -- -- --   (M-final-coalg {S = S} .snd
-- -- -- --     (Σ (M S) (λ a → Σ (M S) (R a)) ,
-- -- -- --      λ { (a , b) → fst (out-fun {S = S} a) , λ x → (snd (out-fun {S = S} a) x) , ((snd (out-fun {S = S} a) x) , R-refl)})
-- -- -- --        .snd (property-2 {S = S} R R-refl) {!!} .fst x)

-- -- -- property : ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ) -> (∀ {x} -> R x x) -> ((x : Σ (M S) (λ a → Σ (M S) (R a))) -> fst (snd x) ≡ fst x) -> bisimulation S M-coalg R
-- -- -- αᵣ (property S R R-refl _) = λ { ( a , b ) → fst (out-fun a) , λ x → (snd (out-fun a) x) , ((snd (out-fun a) x) , R-refl) }
-- -- -- rel₁ (property S R _ _) = funExt λ x → refl
-- -- -- rel₂ (property S R _ R-eq) = funExt λ x i → out-fun {S = S} (R-eq x i)

-- -- -- -------------------------------------------------------------
-- -- -- -- Coinduction principle for M-types (≈ Coinductive types) --
-- -- -- -------------------------------------------------------------

-- -- -- -- coinduction proof by: m ≡ π₁(m,m',r) ≡ π₂(m,m',r) ≡ m' 
-- -- -- coinduction : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> ∀ {m m' : M S} -> R m m' -> m ≡ m' 
-- -- -- coinduction {S = S} R sim {m} {m'} r = λ i -> funExt⁻ (final-property-2 S R sim) (m , (m' , r)) i

-- -- -- coinduction⁻ : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (∀ {x} -> R x x) ->  ∀ {m m' : M S} -> m ≡ m' -> R m m'
-- -- -- coinduction⁻ {S = S} R sim k {m} {m'} r = transp (λ i -> R m (r i)) i0 k

-- -- -- coinduction-iso1 : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (R-refl : ∀ {x} -> R x x) ->
-- -- --                      ∀ {m} {m'} (p : m ≡ m') -> (coinduction R sim {m} {m'}) (coinduction⁻ R sim R-refl p) ≡ p
-- -- -- coinduction-iso1 R sim R-refl p = {!!}

-- -- -- coinduction-iso2 : ∀ {ℓ} {S : Container {ℓ}} R -> (sim : bisimulation S M-coalg R) -> (R-refl : ∀ {x} -> R x x) ->
-- -- --                      ∀ {m} {m'} (p : R m m') -> (coinduction⁻ R sim R-refl (coinduction R sim {m} {m'} p)) ≡ p
-- -- -- coinduction-iso2 R sim R-refl p = {!!}

-- -- -- coinduction-is-equality : ∀ {ℓ} {S : Container {ℓ}} R ->
-- -- --   (sim : bisimulation S M-coalg R) ->
-- -- --   (R-refl : ∀ {x} -> R x x) ->
-- -- --   R ≡ _≡_
-- -- -- coinduction-is-equality R sim R-refl i m m' =
-- -- --   ua (isoToEquiv (
-- -- --     iso
-- -- --       (coinduction R sim {m} {m'})
-- -- --       (coinduction⁻ R sim R-refl)
-- -- --       (coinduction-iso1 R sim R-refl)
-- -- --       (coinduction-iso2 R sim R-refl)
-- -- --     )) i
