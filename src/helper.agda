{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Embedding
open import Cubical.Foundations.FunExtEquiv

module helper where

refl-fun : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
refl-fun x = refl {x = x}

----------------
-- Iso helper --
----------------

open Iso

refl-iso : ∀ {ℓ} {X : Set ℓ} → Iso X X
fun (refl-iso {X = X}) = idfun X
inv (refl-iso {X = X}) = idfun X
rightInv (refl-iso {X = X}) = refl-fun
leftInv (refl-iso {X = X}) = refl-fun

-- Helpful notation
_Iso⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ'} {C : Set ℓ''} (X : Set ℓ) → Iso X B → Iso B C → Iso X C
_ Iso⟨ f ⟩ g = compIso f g

_∎Iso : ∀ {ℓ} (X : Set ℓ) → Iso X X
X ∎Iso = refl-iso {X = X}

infixr  0 _Iso⟨_⟩_
infix   1 _∎Iso

sym-iso : ∀ {ℓ ℓ'} {X : Set ℓ} {Y : Set ℓ'} → Iso X Y → Iso Y X
fun (sym-iso isom) = inv isom
inv (sym-iso isom) = fun isom
rightInv (sym-iso isom) = leftInv isom
leftInv (sym-iso isom) = rightInv isom

--

identity-x : ∀ {ℓ} {A B : Set ℓ} (k : A -> A) -> k ≡ idfun A -> ∀ (x : A) -> k x ≡ x
identity-x {A = A} k = funExt⁻

-- Right
extent-r : ∀ {ℓ} {A B C : Set ℓ} {a b : A -> B} (f : C -> A) -> a ≡ b -> a ∘ f ≡ b ∘ f
extent-r = λ f x i → x i ∘ f

identity-f-r : ∀ {ℓ} {A B : Set ℓ} {k : A -> A} -> k ≡ idfun A -> ∀ (f : B -> A) -> k ∘ f ≡ f
identity-f-r {A = A} {k = k} p f = extent-r {a = k} {b = idfun A} f p

-- Left
extent-l : ∀ {ℓ} {A B C : Set ℓ} {a b : A -> B} (f : B -> C) -> a ≡ b -> f ∘ a ≡ f ∘ b
extent-l = λ f x i → f ∘ x i

identity-f-l : ∀ {ℓ} {A B : Set ℓ} {k : A -> A} -> k ≡ idfun A -> ∀ (f : A -> B) -> f ∘ k ≡ f
identity-f-l {A = A} {k = k} p f = extent-l {a = k} {b = idfun A} f p

-- General

≡-rel-a-monomorphism : ∀ {ℓ} {A B C : Set ℓ} (a : A -> B) (b : B -> A) -> a ∘ b ≡ idfun B -> b ∘ a ≡ idfun A -> {f g : C -> A} -> (a ∘ f ≡ a ∘ g) -> (f ≡ g)
≡-rel-a-monomorphism a b left right {f = f} {g = g} p = λ i →
  compPath-filler {x = f} {y = (b ∘ a ∘ f)} {z = g}
    (sym (identity-f-r right f))
    (λ j → compPath-filler {y = b ∘ a ∘ g}
      (λ k → b ∘ p k)
      (identity-f-r right g)
        j j)
      i i

transport-iso :
  ∀ {ℓ} {X Y : Set ℓ}
  → (isom : Iso X Y)
  → transport (isoToPath isom) ≡ fun isom
transport-iso isom@(iso a b c d) = funExt (λ x → transportRefl (a x))

open import Cubical.Foundations.Equiv.Properties

≡-to-embedding : ∀ {ℓ} {A B C : Set ℓ}
  → (isom : Iso A B)
  -------------------------------
  → isEmbedding (fun isom)
≡-to-embedding {A = A} {B} {C} isom@(iso a b right left) =
  transport
    (cong (λ a₁ → isEmbedding a₁)
     (transport-iso isom))
    (isEquiv→isEmbedding
     (equivIsEquiv
      (pathToEquiv
       (isoToPath isom))))

≡-rel-a-inj' : ∀ {ℓ} {A B C : Set ℓ} (a : A -> B) (e : isEmbedding a) → ∀ {f g : C -> A} -> ∀ x → ((a (f x) ≡ a (g x)) ≡ (f x ≡ g x))
≡-rel-a-inj' a e {f = f} {g} x = sym (ua (cong a , e (f x) (g x)))

≡-rel-a-inj :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B)
  → ∀ {f g : C -> A}
  → ((fun isom) ∘ f ≡ (fun isom) ∘ g) ≡ (f ≡ g)
≡-rel-a-inj {A = A} {B} {C} isom@(iso a b right left) {f = f} {g} =
  a ∘ f ≡ a ∘ g
    ≡⟨ sym funExtPath ⟩
  (∀ x → a (f x) ≡ a (g x))
    ≡⟨ (λ i → ∀ x → ≡-rel-a-inj' {A = A} {B} {C} a (≡-to-embedding {A = A} {B} {C} isom) {f = f} {g = g} x i) ⟩
  (∀ x → f x ≡ g x)
    ≡⟨ funExtPath ⟩
  f ≡ g ∎

≡-rel-b-inj :
  ∀ {ℓ} {A B C : Set ℓ} (isom : Iso A B) →
  ∀ {f g : C -> B} →
  -----------------------
  ((inv isom) ∘ f ≡ (inv isom) ∘ g) ≡ (f ≡ g)
≡-rel-b-inj {A = A} {B} {C} isom@(iso a b right left) {f = f} {g} =
  b ∘ f ≡ b ∘ g
    ≡⟨ sym funExtPath ⟩
  (∀ x → b (f x) ≡ b (g x))
    ≡⟨ (λ i → ∀ x → ≡-rel-a-inj' {A = B} {A} {C} b (≡-to-embedding {A = B} {A} {C} (sym-iso isom)) {f = f} {g = g} x i) ⟩
  (∀ x → f x ≡ g x)
    ≡⟨ funExtPath ⟩
  f ≡ g ∎

≡-rel-a-inj-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : A}
  → ((fun isom) x ≡ (fun isom) y) ≡ (x ≡ y)
≡-rel-a-inj-x isom {x} {y} =
  let tempx = λ {(lift tt) → x}
      tempy = λ {(lift tt) → y} in
   fun isom x ≡ fun isom y
      ≡⟨ isoToPath (iso (λ x₁ t → x₁)
                        (λ x₁ → x₁ (lift tt))
                        (λ b → refl)
                        (λ a → refl)) ⟩
  (∀ (t : Lift Unit) -> (((fun isom) ∘ tempx) t ≡ ((fun isom) ∘ tempy) t))
    ≡⟨ funExtPath ⟩
  ((fun isom) ∘ tempx) ≡ ((fun isom) ∘ tempy)
    ≡⟨ ≡-rel-a-inj isom ⟩
  tempx ≡ tempy
    ≡⟨ sym (funExtPath) ⟩
  (∀ (t : Lift Unit) -> tempx t ≡ tempy t)
    ≡⟨ isoToPath (iso (λ x₁ → x₁ (lift tt))
                      (λ x₁ t → x₁)
                      (λ b → refl)
                      (λ a → refl)) ⟩
  x ≡ y ∎

≡-rel-b-inj-x :
  ∀ {ℓ} {A B : Set ℓ}
  → (isom : Iso A B)
  → ∀ {x y : B}
  → ((inv isom) x ≡ (inv isom) y) ≡ (x ≡ y)
≡-rel-b-inj-x isom = ≡-rel-a-inj-x (sym-iso isom)

-------------------------
-- Unit / × properties --
-------------------------

diagonal-unit : ∀ {ℓ} → Lift {ℓ-zero} {ℓ} Unit ≡ Lift {ℓ-zero} {ℓ} Unit × Lift {ℓ-zero} {ℓ} Unit
diagonal-unit = isoToPath (iso (λ x → (lift tt) , (lift tt)) (λ x → lift tt) (λ {(lift tt , lift tt) i → (lift tt) , (lift tt)}) λ {(lift tt) i → lift tt})

------------------
-- Σ properties --
------------------

Σ-split-iso : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {a a' : A} {b : B a} {b' : B a'} → Iso (Σ (a ≡ a') (λ q → PathP (λ i → B (q i)) b b')) ((a , b) ≡ (a' , b'))
fun (Σ-split-iso) = ΣPathP
inv (Σ-split-iso) eq = (λ i → fst (eq i)) , (λ i → snd (eq i))
rightInv (Σ-split-iso) = refl-fun
leftInv (Σ-split-iso) = refl-fun

Σ-split : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {a a' : A} {b : B a} {b' : B a'} → (Σ (a ≡ a') (λ q → PathP (λ i → B (q i)) b b')) ≡ ((a , b) ≡ (a' , b'))
Σ-split = ua Σ≡

Σ-split-iso' : ∀ {ℓ} {A B : Set ℓ} {a a' : A} {b' b : B} → (Σ (a ≡ a') (λ q → b ≡ b')) ≡ ((a , b) ≡ (a' , b'))
Σ-split-iso' = ua Σ≡

subst-hom : ∀ {i j} {X : Set i}(P : X → Set j){x y z : X}
          → (p : x ≡ y)(q : y ≡ z)(u : P x)
          → subst P q (subst P p u) ≡ subst P (p □ q) u
subst-hom {X = X} P {x = x} {y = y} {z = z} p q u = sym (substComposite-□ P p q u)

Σ-ap-iso₂ : ∀ {i j} {X : Set i}
          → {Y Y' : X → Set j}
          → ((x : X) → Iso (Y x) (Y' x))
          → Iso (Σ X Y)
                 (Σ X Y')
fun (Σ-ap-iso₂ {X = X} {Y} {Y'} isom) (x , y) = x , fun (isom x) y
inv (Σ-ap-iso₂ {X = X} {Y} {Y'} isom) (x , y') = x , inv (isom x) y'
rightInv (Σ-ap-iso₂ {X = X} {Y} {Y'} isom) (x , y) = ΣPathP (refl , rightInv (isom x) y)
leftInv (Σ-ap-iso₂ {X = X} {Y} {Y'} isom) (x , y') = ΣPathP (refl , leftInv (isom x) y')

Σ-ap₂ : ∀ {i j} {X : Set i}
          → {Y Y' : X → Set j}
          → ((x : X) → Y x ≡ Y' x)
          → Σ X Y ≡ Σ X Y'
Σ-ap₂ {X = X} {Y} {Y'} isom = isoToPath (Σ-ap-iso₂ (pathToIso ∘ isom))

sym-refl : ∀ {ℓ} {X Y : Set ℓ} {f : X → Y} {g : Y → X} → (a : (∀ b → f (g b) ≡ b)) → ∀ b → (sym (a b) □ (a b)) ≡ λ _ → b
sym-refl a b =
  (sym (a b) □ (a b))
    ≡⟨ □≡∙ (sym (a b)) (a b) ⟩
  sym (a b) ∙ (a b)
    ≡⟨ lUnit (sym (a b) ∙ (a b)) ⟩
  refl ∙ sym (a b) ∙ (a b)
    ≡⟨ assoc refl (sym (a b)) (a b) ⟩
  (refl ∙ sym (a b)) ∙ (a b)
    ≡⟨ compPathr-cancel (a b) refl ⟩
  refl ∎

Σ-ap-iso₁ : ∀ {i} {X X' : Set i} {Y : X' → Set i}
          → (isom : Iso X X')
          → Iso (Σ X (Y ∘ (fun isom)))
                 (Σ X' Y)
fun (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom@(iso f g K H)) x = f (x .fst) , x .snd
inv (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom@(iso f g K H)) x = g (x .fst) , subst Y (sym (K (x .fst))) (x .snd)
rightInv (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom@(iso f g K H)) (x , y) = ΣPathP (K x ,
  transport (sym (PathP≡Path (λ j → cong Y (K x) j) (subst Y (sym (K x)) y) y))
            (subst Y (K x) (subst Y (sym (K x)) y)
              ≡⟨ sym (substComposite-□ Y (sym (K x)) (K x) y) ⟩
            subst Y ((sym (K x)) □ (K x)) y
              ≡⟨ (cong (λ a → subst Y a y) (sym-refl {f = f} {g = g} K x)) ⟩
            subst Y refl y
              ≡⟨ substRefl {B = Y} y ⟩
            y ∎))
leftInv (Σ-ap-iso₁ {i} {X = X} {X'} {Y} isom@(iso f g K H)) (x , y) = ΣPathP (H x ,
  transport (sym (PathP≡Path (λ j → Y (f (H x j))) (subst Y (sym (K (f x))) y) y))
            (subst Y (cong f (H x)) (subst Y (sym (K (f x))) y)
              ≡⟨ sym (substComposite-□ Y (sym (K (f x))) (λ j → f (H x j)) y) ⟩
            subst Y (sym (K (f x)) □ (cong f (H x))) y
              ≡⟨ cong (λ a → subst Y (sym (K (f x)) □ a) y) lem ⟩
            subst Y (sym (K (f x)) □ K (f x)) y
              ≡⟨ cong (λ a → subst Y a y) (sym-refl {f = f} {g = g} K (f x)) ⟩
            subst Y (refl) y
              ≡⟨ substRefl {B = Y} y ⟩
            y ∎))
  where
    postulate
      lem : cong f (H x) ≡ K (f x)  -- Vogt lemma -- law of excluded middle -- Hfa≡fHa (equiv)

Σ-ap₁ : ∀ {i} {X X' : Set i} {Y : X' → Set i}
          → (isom : X ≡ X')
          → Σ X (Y ∘ transport isom) ≡ Σ X' Y
Σ-ap₁ {i} {X = X} {X'} {Y} isom = isoToPath (Σ-ap-iso₁ (pathToIso isom))

Σ-ap-iso : ∀ {i} {X X' : Set i}
           {Y : X → Set i} {Y' : X' → Set i}
         → (isom : Iso X X')
         → ((x : X) → Iso (Y x) (Y' (fun isom x)))
         → Iso (Σ X Y)
                (Σ X' Y')
Σ-ap-iso {X = X} {X'} {Y} {Y'} isom isom' = compIso (Σ-ap-iso₂ isom') (Σ-ap-iso₁ isom)

Σ-ap :
  ∀ {i} {X X' : Set i} {Y : X → Set i} {Y' : X' → Set i}
  → (isom : X ≡ X')
  → ((x : X) → Y x ≡ Y' (transport isom x))
  ----------
  → (Σ X Y)
  ≡ (Σ X' Y')
Σ-ap  {X = X} {X'} {Y} {Y'} isom isom' = isoToPath (Σ-ap-iso (pathToIso isom) (pathToIso ∘ isom'))

Σ-ap' :
  ∀ {ℓ} {X X' : Set ℓ} {Y : X → Set ℓ} {Y' : X' → Set ℓ}
  → (isom : X ≡ X')
  → (PathP (λ i → isom i → Set _) Y Y')
  ----------
  → (Σ X Y)
  ≡ (Σ X' Y')
Σ-ap'  {ℓ} {X = X} {X'} {Y} {Y'} isom isom' = cong₂ (λ (a : Set ℓ) (b : a → Set ℓ) → Σ a λ x → b x) isom isom'

------------------
-- ∏ properties --
------------------

coherent : ∀ {i j} {X : Set i} {Y : Set j} → Iso X Y → Set _
coherent = λ x → ∀ f -> cong (fun x) (leftInv x f) ≡ rightInv x (fun x f)

coherent' : ∀ {i j} {X : Set i}{Y : Set j} → Iso X Y → Set _
coherent' f = ∀ y → cong (inv f) (rightInv f y) ≡ leftInv f (inv f y)

asdf : ∀ {i j} (X : Set i) (Y : Set j) → Set _
asdf X Y = Σ (Iso X Y) coherent

postulate
  ap' : ∀ {i j} {X : Set i}{Y : X → Set j}
        {x x' : X}(f : (x : X) → Y x)(p : x ≡ x')
      → subst Y p (f x) ≡ f x'
-- ap' a b = {!!}

subst-naturality : ∀ {i i' j} {X : Set i} {Y : Set i'}
                   {x x' : X} (P : Y → Set j)
                   (f : X → Y)(p : x ≡ x')(u : P (f x))
                 → subst (P ∘ f) p u ≡ subst P (cong f p) u
subst-naturality _ _ _ _ = refl

-- technical lemma: substiting a fixpoint proof into itself is like
-- applying the function
lem-subst-fixpoint : ∀ {i}{X : Set i}
                     (f : X → X)(x : X)
                     (p : f x ≡ x)
                   → subst (λ x → f x ≡ x) (sym p) p
                   ≡ cong f p
lem-subst-fixpoint {i}{X} f x p =
    subst (λ x → f x ≡ x) (p ⁻¹) p
  ≡⟨ lem (f x) (sym p) ⟩ 
    cong f (sym (sym p)) ∙ p ∙ sym p
  ≡⟨ cong (λ z → cong f z ∙ p ∙ sym p) (symInvo p) ⟩ -- (double-inverse p) ⟩
    cong f p ∙ p ∙ sym p
  ≡⟨ refl ⟩ -- associativity (ap f p) p (sym p)
    cong f p ∙ (p ∙ sym p)
  ≡⟨ cong (λ z → cong f p ∙ z) (rCancel p) ⟩ -- (left-inverse p)
    cong f p ∙ refl
  ≡⟨ sym (rUnit (cong f p)) ⟩
    cong f p
  ∎
  where
    postulate
      lem : (y : X) (q : x ≡ y)
        → subst (λ z → f z ≡ z) q p
        ≡ cong f (sym q) ∙ p ∙ q
    -- lem y q = {!!} -- sym (lUnit p)
    
lem-whiskering : ∀ {i} {X : Set i}
                 (f : X → X) (H : (x : X) → f x ≡ x)
                 (x : X) → cong f (H x) ≡ H (f x)
lem-whiskering f H x =
    cong f (H x)
  ≡⟨ sym (lem-subst-fixpoint f x (H x)) ⟩
    subst (λ z → f z ≡ z) (sym (H x)) (H x)
  ≡⟨ ap' H (sym (H x)) ⟩
    H (f x)
  ∎
    
co-coherence : ∀ {i j}{X : Set i}{Y : Set j}
               (isom : Iso X Y)
             → coherent isom
             → coherent' isom
co-coherence (iso f g K H) coherence y =
  subst (λ z → cong g (K z) ≡ H (g z)) (K y) lem
  where
    postulate
      lem : cong g (K (f (g y)))
        ≡ H (g (f (g y)))
    -- lem = 
    --     cong g (K (f (g y)))
    --   ≡⟨ cong (cong g) (sym (coherence (g y))) ⟩
    --     cong g (cong f (H (g y)))
    --   ≡⟨ {!!} ⟩ -- ap-hom f g _
    --     cong (g ∘ f) (H (g y))
    --   ≡⟨ lem-whiskering (g ∘ f) H (g y) ⟩
    --     H (g (f (g y)))
    --   ∎

postulate
  Π-iso :
    ∀ {i i' j} {X : Set i} {X' : Set i'} {Y : X → Set j} {Y' : X' → Set j}
    (isom : Iso X X')
    → (Iso ((x : X) → Y x) ((x' : X') → Y (inv isom x')))
-- Π-iso {X = X}  {X'} {Y} {Y'} (iso f g K H) =
--   iso (λ h x' → h (g x'))
--       (λ h' x → subst Y (H x) (h' (f x)))
--       (λ h' → funExt λ x' → cong (λ p → subst Y p _) (sym {!!}) ∙ sym (subst-naturality Y g (K x') _) ∙ ap' h' (K x'))
--       (λ h → funExt λ x → ap' h (H x))
--   where γ' = {!!} -- co-coherence (iso f g H K) γ

  
-- record
      -- { to = λ h x' → h (g x')
      -- ; from = λ h' x → subst Y (H x) (h' (f x))
      -- ; iso₁ = λ h → funext λ x → ap' h (H x)
      -- ; iso₂ = λ h' → funext λ x' →
      --         ap (λ p → subst Y p _) (sym (γ' x'))
      --       · sym (subst-naturality Y g (K x') _)
      --       · ap' h' (K x') }

-- where γ' = co-coherence (iso f g H K) γ

postulate
  Π-ap-iso : ∀ {i i' j}{X : Set i}{X' : Set i'}
             {Y : X → Set j}{Y' : X' → Set j}
           → (isom : Iso X X')
           → ((x' : X') → Iso (Y (inv isom x')) (Y' x'))
           → Iso ((x : X) → Y x)
                 ((x' : X') → Y' x')
-- Π-ap-iso {X = X}{X'}{Y}{Y'} isom isom' =
--   iso (λ x x' → {!!}) {!!} {!!} {!!}

postulate
  -- ∏-ap-iso :
  --   ∀ {i j} {X X' : Set i} {Y : X → Set j} {Y' : X' → Set j}
  --   → (isom : Iso X X')
  --   → ((x' : X') → Y (inv isom x') ≡ Y' x')
  --   → Iso ((x : X) → Y x)
  --          ((x' : X') → Y' x')

  ∏-ap :
    ∀ {i j} {X X' : Set i} {Y : X → Set j} {Y' : X' → Set j}
    → (isom : X ≡ X')
    → ((x' : X') → Y (transport (sym isom) x') ≡ Y' x')
    → ((x : X) → Y x)
    ≡ ((x' : X') → Y' x')
