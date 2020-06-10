{-# OPTIONS --cubical --guardedness #-} 
module QPF-multiset where

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

open import QPF

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

-- Construction of MS from a QPF
-- QPF formalization of multisets
∼perm' : {R : Type₀} {X : Type₀} {a : tree-S R .fst} → (tree-S R .snd a → X) → (tree-S R .snd a → X) → Type₀
∼perm' {a = inr tt} f h = Σ[ g ∈ (ℕ → ℕ) ] (isEquiv g × (f ∘ g ≡ h))
∼perm' {a = inl r} _ _ = Unit

∼perm'-comm :  {R : Type₀} {X Y : Type₀} (f : X → Y) {a : tree-S R .fst} → {x y : tree-S R .snd a → X} → ∼perm' x y → ∼perm' (f ∘ x) (f ∘ y)
∼perm'-comm f {a = inr tt} p = (p .fst) , ((proj₁ (p .snd)) , cong (λ a → f ∘ a) (proj₂ (p .snd)))

∼perm'-comm f {a = inl r} tt = tt

multiset : ∀ {R} → poly-quot (tree-S R) ∼perm' ∼perm'-comm
multiset {R = R} = poly-quot-constr (tree-S R) ∼perm' ∼perm'-comm
