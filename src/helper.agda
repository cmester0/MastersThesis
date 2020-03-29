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

-- (a : A -> B) (b : B -> A) -> a ∘ b ≡ idfun B -> b ∘ a ≡ idfun A

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

postulate
  ∏-ap-iso :
    ∀ {i j} {X X' : Set i} {Y : X → Set j} {Y' : X' → Set j}
    → (isom : Iso X X')
    → ((x' : X') → Y (inv isom x') ≡ Y' x')
    → Iso ((x : X) → Y x)
           ((x' : X') → Y' x')

  ∏-ap :
    ∀ {i j} {X X' : Set i} {Y : X → Set j} {Y' : X' → Set j}
    → (isom : X ≡ X')
    → ((x' : X') → Y (transport (sym isom) x') ≡ Y' x')
    → ((x : X) → Y x)
    ≡ ((x' : X') → Y' x')

------------------------
-- Unit / Contractive --
------------------------

IsoToiso-Iso : Iso (Iso Unit Unit) (Unit ≃ Unit)
fst (fun IsoToiso-Iso x) = fun x
snd (fun IsoToiso-Iso x) .equiv-proof = λ y → (tt , refl) , (λ y₁ i → tt , refl)
inv IsoToiso-Iso = λ x → iso (λ x₁ → tt) (λ x₁ → tt) (λ b i → tt) λ a i → tt
fst (rightInv IsoToiso-Iso b i) = (λ x → tt)
snd (rightInv IsoToiso-Iso b i) .equiv-proof = λ y → (tt , (λ i₁ → tt)) , (λ y₁ i₁ → tt , (λ i₂ → tt))
leftInv IsoToiso-Iso = refl-fun

IsoToiso : (Iso Unit Unit) ≡ (Unit ≃ Unit)
IsoToiso = isoToPath IsoToiso-Iso

isis : isContr (Unit ≃ Unit) ≡ isContr (Iso Unit Unit)
isis = cong isContr (sym IsoToiso) 

unit-Iso-is-contractive : isContr (Iso Unit Unit)
unit-Iso-is-contractive = iso (λ _ → tt) (λ _ → tt) refl-fun refl-fun , (λ y → refl)

unit-≃-is-contractive : isContr (Unit ≃ Unit)
unit-≃-is-contractive = transport (sym isis) unit-Iso-is-contractive

lift-contr→contr-lift-Iso : Iso (Lift {ℓ-zero} {ℓ-suc ℓ-zero} (isContr (Unit ≃ Unit))) (isContr (Lift {ℓ-zero} {ℓ-suc ℓ-zero} (Unit ≃ Unit)))
fun lift-contr→contr-lift-Iso x = (lift (lower x .fst)) , (λ y → cong lift (lower x .snd (lower y)))
inv lift-contr→contr-lift-Iso x = lift ((lower (x .fst)) , (λ y → cong lower (x .snd (lift y))))
rightInv lift-contr→contr-lift-Iso = refl-fun
leftInv lift-contr→contr-lift-Iso = refl-fun

lift-contr→contr-lift : Lift {ℓ-zero} {ℓ-suc ℓ-zero} (isContr (Unit ≃ Unit)) ≡ isContr (Lift {ℓ-zero} {ℓ-suc ℓ-zero} (Unit ≃ Unit))
lift-contr→contr-lift = isoToPath lift-contr→contr-lift-Iso

unit-≃-is-contractive-lift : isContr (Lift {ℓ-zero} {ℓ-suc ℓ-zero} (Unit ≃ Unit))
unit-≃-is-contractive-lift = transport lift-contr→contr-lift (lift unit-≃-is-contractive)

unit-≡-is-contractive : isContr (Unit ≡ Unit)
unit-≡-is-contractive = transport (cong isContr (sym univalencePath)) unit-≃-is-contractive-lift

inr-inj-unit : ∀ {R : Set} (a b : R) → (inr {A = Unit} {B = R} a ≡ inr b) ≡ (a ≡ b)
inr-inj-unit a b =
  (sym (ua (SumPath.Cover≃Path (inr a) (inr b)))) □ isoToPath (iso lower lift refl-fun refl-fun)

transportComposite-□ : ∀ {ℓ} {A B C : Set ℓ} (p : A ≡ B) (q : B ≡ C) (x : A) → transport (p □ q) x ≡ transport q (transport p x)
transportComposite-□ p q x = substComposite-□ (λ x₁ → x₁) p q x

postulate
  ad : ∀ {ℓ} {A B C : Set ℓ} (p : A ≡ B) (q : B ≡ C) → sym (p □ q) ≡ sym q □ sym p

ass : ∀ {ℓ} {A B C : Set ℓ} (p : A ≡ B) (q : B ≡ C) (x : C) → transport⁻ (p □ q) x ≡ transport⁻ p (transport⁻ q x)
ass p q x =
  transport⁻ (p □ q) x
    ≡⟨ refl ⟩
  transport (sym (p □ q)) x
    ≡⟨ cong (λ a → transport a x) (ad p q) ⟩
  transport (sym q □ sym p) x
    ≡⟨ transportComposite-□ (sym q) (sym p) x ⟩
  transport⁻ p (transport⁻ q x) ∎

asdf : ∀ {R} (r s : R) x → cong inr x ≡ transport⁻ (inr-inj-unit r s) x
asdf r s x =
  cong inr x
    ≡⟨ refl ⟩
  SumPath.decode (inr r) (inr s) (lift x)
    ≡⟨ sym (uaβ (SumPath.Cover≃Path (inr r) (inr s)) (lift x)) ⟩
  transport (ua (SumPath.Cover≃Path (inr r) (inr s))) (lift x)
    ≡⟨ refl ⟩
  transport⁻ (sym (ua (SumPath.Cover≃Path (inr r) (inr s)))) (lift x)
    ≡⟨ cong (transport⁻ (sym (ua (SumPath.Cover≃Path (inr r) (inr s))))) (sym (uaβ (isoToEquiv (iso lift lower refl-fun refl-fun)) x)) ⟩
  transport⁻ (sym (ua (SumPath.Cover≃Path (inr r) (inr s)))) (transport (ua (isoToEquiv (iso lift lower refl-fun refl-fun))) x)
    ≡⟨ refl ⟩
  transport⁻ (sym (ua (SumPath.Cover≃Path (inr r) (inr s)))) (transport (isoToPath (iso lift lower refl-fun refl-fun)) x)
    ≡⟨ refl ⟩
  transport⁻ (sym (ua (SumPath.Cover≃Path (inr r) (inr s)))) (transport⁻ (isoToPath (iso lower lift refl-fun refl-fun)) x)
    ≡⟨ sym (ass (sym (ua (SumPath.Cover≃Path (inr r) (inr s)))) (isoToPath (iso lower lift refl-fun refl-fun)) x) ⟩
  transport⁻ (sym (ua (SumPath.Cover≃Path (inr r) (inr s))) □ isoToPath (iso lower lift refl-fun refl-fun)) x
    ≡⟨ refl ⟩
  transport⁻ (inr-inj-unit r s) x ∎

inr-contractive : ∀ {R} (r s : R) → isContr (r ≡ s) → isContr (inr {A = Unit} r ≡ inr s)
inr-contractive r s x = cong inr (x .fst) , λ y →
  cong inr (x .fst)
    ≡⟨ cong (cong inr) (x .snd (transport (inr-inj-unit r s) y)) ⟩
  cong inr (transport (inr-inj-unit r s) y)
    ≡⟨ asdf r s (transport (inr-inj-unit r s) y) ⟩
  transport⁻ (inr-inj-unit r s) (transport (inr-inj-unit r s) y)
    ≡⟨ transport⁻Transport (inr-inj-unit r s) y ⟩
  y ∎

postulate
  wanting : ∀ {ℓ} {R M : Set ℓ} (r s : R) (f : R → M) → (x : isContr (f r ≡ f s)) → ∀ (i : I) → Σ R λ y → x .fst i ≡ f y
