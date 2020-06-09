{-# OPTIONS --cubical --guardedness #-}

module QPF where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Bool

open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.helper

open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.HITs.SetQuotients renaming (elim to elim/)
open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥ ; rec to ∥rec∥ ; elim to ∥elim∥)

open import helper renaming (rec to rec/)

-- Tree defined as an M-type
tree-S : (R : Type₀) -> Container ℓ-zero
tree-S R = (R ⊎ Unit) , λ { (inl _) -> ⊥ ; (inr tt) -> ℕ }

tree : (R : Type₀) -> Type₀
tree R = M (tree-S R)

leaf : {R : Type₀} -> R -> tree R
leaf r = in-fun (inl r , λ ())

node : {R : Type₀} -> (ℕ → tree R) -> tree R
node f = in-fun (inr tt , f)

-- Weak bisimularity for tree (defining multisets)
data _∼_ {R : Type₀} : (_ _ : tree R) → Type₀ where
  ∼now : ∀ (s r : R) → s ≡ r → leaf s ∼ leaf r
  ∼later : ∀ f g → (∀ n → f n ∼ g n) → node f ∼ node g
  ∼perm : ∀ f (g : ℕ → ℕ) → isEquiv g → node f ∼ node (f ∘ g)

Quotient-Container : ∀ {ℓ} → (S : Container ℓ) → (R : {a : S .fst} → (Σ ((S .snd a) → (S .snd a) → Type ℓ) λ G → isEquiv G)) → Container ℓ
Quotient-Container (A , B) G = A , λ a → let (R , e) = G {a = a} in B a / R

F : ∀ {ℓ} → (S : Container ℓ) → (R : {a : S .fst} → (Σ ((S .snd a) → (S .snd a) → Type ℓ) λ G → isEquiv G)) → Type ℓ → Type ℓ
F S R = P₀ (Quotient-Container S R)

QPF₀ : ∀ {ℓ} → (S : Container ℓ) → ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ) → Type ℓ → Type ℓ
QPF₀ (A , B) ∼ₛ X = Σ[ a ∈ A ] ((B a → X) / ∼ₛ {a = a})

QPF₁ :
  ∀ {ℓ} → (S : Container ℓ) → {X Y : Type ℓ}
  → (∼ₛ : {X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)
  → (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → ∼ₛ x y → ∼ₛ (f ∘ x) (f ∘ y))
  → (f : X → Y)
  → QPF₀ S ∼ₛ X → QPF₀ S ∼ₛ Y
QPF₁ S {X = X} {Y = Y} ∼ₛ ∼ₛ-comp f (a , g) =
  a ,
  elim/
    {A = S .snd a → X}
    {R = ∼ₛ}
    {B = λ _ → (S .snd a → Y) / ∼ₛ}
    (λ x → squash/)
    (λ g → [ f ∘ g ])
    (λ x y r → eq/ (f ∘ x) (f ∘ y) (∼ₛ-comp f r))
    g

Wₙ' : ∀ {ℓ} -> (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) -> ℕ -> Type ℓ
Wₙ' S R 0 = Lift Unit
Wₙ' S R (suc n) = QPF₀ S R (Wₙ' S R n)

πₙ' : ∀ {ℓ} -> (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) -> {n : ℕ} -> Wₙ' S R (suc n) -> Wₙ' S R n
πₙ' _ _ _ {0} _ = lift tt
πₙ' S R R-comm {suc n} = QPF₁ S R R-comm (πₙ' S R R-comm {n})

sequence' : ∀ {ℓ} -> (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) -> Chain ℓ
X (sequence' S R R-comm) n = Wₙ' S R n
π (sequence' S R R-comm) {n} = πₙ' S R R-comm {n}

QM : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → Type ℓ
QM S R R-comm = limit-of-chain (sequence' S R R-comm)

poly-quot : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → Set (ℓ-suc ℓ)
poly-quot {ℓ} S R R-comm =
  Σ[ abs ∈ ({X : Set ℓ} → P₀ S X → QPF₀ S R X) ]
    ((∀ {X} → isSurjection (abs {X})) × ({X Y : Set ℓ} (f : X → Y) (x : P₀ S X) → abs (P₁ f x) ≡ QPF₁ S R R-comm f (abs x))) -- Is one of these properties not enought?

poly-quot-constr : {ℓ : Level} (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → poly-quot S R R-comm
poly-quot-constr S R R-comm =
  (λ {(a , b) → a , [ b ]}) ,
  (λ {(a , b) → ∥map∥ (λ {(g , p) → (a , g) , ((a , [ g ]) ≡⟨ ΣPathP (refl , p) ⟩ (a , b) ∎)}) ([]surjective b) }) ,
  λ {f (a , b) → refl}

-- QPF formalization of multisets
∼perm' : {R : Type₀} {X : Type₀} {a : tree-S R .fst} → (tree-S R .snd a → X) → (tree-S R .snd a → X) → Type₀
∼perm' {a = inr tt} f h = Σ[ g ∈ (ℕ → ℕ) ] (isEquiv g × (f ∘ g ≡ h))
∼perm' {a = inl r} _ _ = Unit

∼perm'-comm :  {R : Type₀} {X Y : Type₀} (f : X → Y) {a : tree-S R .fst} → {x y : tree-S R .snd a → X} → ∼perm' x y → ∼perm' (f ∘ x) (f ∘ y)
∼perm'-comm f {a = inr tt} p = (p .fst) , ((proj₁ (p .snd)) , cong (λ a → f ∘ a) (proj₂ (p .snd)))

∼perm'-comm f {a = inl r} tt = tt

multiset : ∀ {R} → poly-quot (tree-S R) ∼perm' ∼perm'-comm
multiset {R = R} = poly-quot-constr (tree-S R) ∼perm' ∼perm'-comm






