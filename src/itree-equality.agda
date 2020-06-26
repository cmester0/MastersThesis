{-# OPTIONS --cubical --guardedness #-} --safe

module itree-equality where

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to empty-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥)
open import Cubical.HITs.SetQuotients renaming (elim to elim/)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv

open import Cubical.Codata.M.AsLimit.Container
open import M
open import Coalg.Coinduction
open import Coalg.Properties

open import Cubical.Foundations.HLevels
open import helper renaming (rec to rec/)

-- Bottom element raised
data ⊥₁ : Type₁ where

rec₁ : ∀ {ℓ} {A : Type ℓ} → ⊥₁ → A
rec₁ ()

elim₁ : ∀ {ℓ} {A : ⊥₁ → Type ℓ} → (x : ⊥₁) → A x
elim₁ ()

isContr⊥₁→A : ∀ {ℓ} {A : Type ℓ} → isContr (⊥₁ → A)
fst isContr⊥₁→A ()
snd isContr⊥₁→A f i ()

-- ITrees (and buildup examples)
-- https://arxiv.org/pdf/1906.00046.pdf
-- Interaction Trees: Representing Recursive and Impure Programs in Coq
-- Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, Steve Zdancewic

itree-S : ∀ (E : Type₀ -> Type₁) (R : Type₀) -> Container (ℓ-suc ℓ-zero)
itree-S E R = ((Unit ⊎ R) ⊎ (Σ[ A ∈ Type₀ ] (E A))) , (λ { (inl (inl _)) -> Lift Unit ; (inl (inr _)) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

itree :  ∀ (E : Type₀ -> Type₁) (R : Type₀) -> Type₁
itree E R = M (itree-S E R)

ret' : ∀ {E} {R}  -> R -> P₀ (itree-S E R) (itree E R)
ret' {E} {R} r = inl (inr r) , λ ()

tau' : {E : Type₀ -> Type₁} -> {R : Type₀} -> itree E R -> P₀ (itree-S E R) (itree E R)
tau' t = inl (inl tt) , λ _ → t

vis' : ∀ {E} {R}  -> ∀ {A : Type₀} -> E A -> (A -> itree E R) -> P₀ (itree-S E R) (itree E R)
vis' {A = A} e k = inr (A , e) , (λ {(lift x) → k x})

ret : ∀ {E} {R}  -> R -> itree E R
ret = in-fun ∘ ret'

tau : {E : Type₀ -> Type₁} -> {R : Type₀} -> itree E R -> itree E R
tau = in-fun ∘ tau'

vis : ∀ {E} {R}  -> ∀ {A : Type₀} -> E A -> (A -> itree E R) -> itree E R
vis {A = A} e = in-fun ∘ (vis' {A = A} e)

data _∼_ {E R} : itree E R → itree E R → Set₁ where
  ∼ret : ∀ {a b} → a ≡ b → ret a ∼ ret b
  ∼tau : ∀ {t u} → t ∼ u → tau t ∼ tau u
  ∼vis : ∀ {A} {e : E A} {k1 k2 : A → itree E R}
         → (∀ x → k1 x ∼ k2 x) → vis e k1 ∼ vis e k2  

-- postulate
asfd' : ∀ {E} {R} A (e : E A) k1 → out-fun (vis {E} {R} {A = A} e k1) ≡ (inr (A , e) , λ {(lift x) → k1 x})
asfd' A e k1 i = out-inverse-in i (inr (A , e) , (λ {(lift x) → k1 x}))

open bisimulation

itree-bisim : ∀ {E R} → bisimulation (itree-S E R) M-coalg _∼_
αᵣ (itree-bisim {E} {R}) (x , y , ∼ret {a} p) = inl (inr a) , λ _ → x , (y , ∼ret p)
αᵣ (itree-bisim {E} {R}) (x , y , ∼tau {t} {u} p) = inl (inl tt) , λ _ → t , (u , p)
αᵣ (itree-bisim {E} {R}) (x , y , ∼vis {A} {e} {k1} {k2} r) = inr (A , e) , λ v → k1 (lower v) , (k2 (lower v) , r (lower v))
rel₁ (itree-bisim {E} {R}) = funExt temp
  where
    temp : ∀ x → M-coalg .snd (fst x) ≡ P₁ fst (αᵣ itree-bisim x)
    temp (x , y , ∼ret {a} {b} p) = ΣPathP (refl , isContr→isProp isContr⊥₁→A (snd (out-fun x)) (λ _ → ret a))
    temp (x , y , ∼tau {t} {u} p) = ΣPathP (refl , λ i → snd (out-inverse-in i (inl (inl tt) , λ _ → t)))
    temp (x , y , ∼vis {A} {e} {k1} {k2} r) = ΣPathP (refl , cong snd (asfd' A e k1))
rel₂ (itree-bisim {E} {R}) = funExt temp
  where
    temp : ∀ x → M-coalg .snd (fst (snd x)) ≡ P₁ (fst ∘ snd) (αᵣ itree-bisim x)
    temp (x , y , ∼ret {a} {b} p) = ΣPathP (cong (inl ∘ inr) (sym p) , isContr→isProp isContr⊥₁→A (snd (out-fun y)) (λ _ → ret b))
    temp (x , y , ∼tau {t} {u} p) = ΣPathP (refl , λ i → snd (out-inverse-in i (inl (inl tt) , λ _ → u)))
    temp (x , y , ∼vis {A} {e} {k1} {k2} r) = ΣPathP (refl , cong snd (asfd' A e k2))

itree-coinduction : ∀ {E} {R} {x y : itree E R} → x ∼ y → x ≡ y
itree-coinduction = coinduction _∼_ itree-bisim
