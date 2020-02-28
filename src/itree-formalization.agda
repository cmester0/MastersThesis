{-# OPTIONS --cubical --guardedness #-} --safe

open import M
open import Coalg
open import itree-extended

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetQuotients
open import Cubical.Foundations.Univalence

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

module itree-formalization where

QM : ∀ {ℓ} (S : Container {ℓ}) (R : M S -> M S -> Set ℓ) -> Set ℓ
QM S R = M S / R

mutual
  data _wITp≈_ {E} {R} : P₀ {S = itree-S E R} (itree E R) -> P₀ {S = itree-S E R} (itree E R) -> Set₁ where -- weak itree approx
    EqRetP : ∀ {r s} -> r ≡ s -> ∀ {b} -> (retT r , b) wITp≈ (retT s , b) -- ret' r , ret' s
    EqTauP : ∀ {t u} -> t wIT≈ u -> tau' t wITp≈ tau' u
    EqTauLP : ∀ {t u} -> t wIT≈ in-fun u -> tau' t wITp≈ u
    EqTauRP : ∀ {t u} -> in-fun t wIT≈ u -> t wITp≈ tau' u
    EqVisP : ∀ {A e k1 k2} -> k1 ≡ k2 -> vis' {A = A} e k1 wITp≈ vis' e k2

  data _wIT≈_ {E} {R} : itree E R -> itree E R -> Set₁ where
    constr : ∀ x y -> (out-fun x) wITp≈ (out-fun y) -> x wIT≈ y

  -- data _wIT≈_ {E} {R} : itree E R -> itree E R -> Set₁ where -- weak itree approx
  --   EqRet : ∀ {r s} -> r ≡ s -> ∀ {b} -> in-fun (retT r , b) wIT≈ in-fun (retT s , b) -- ret s , ret r
  --   EqTau : ∀ {t u} -> t wIT≈ u -> tau t wIT≈ tau u
  --   EqTauL : ∀ {t u} -> t wIT≈ u -> tau t wIT≈ u
  --   EqTauR : ∀ {t u} -> t wIT≈ u -> t wIT≈ tau u
  --   EqVis : ∀ {A e k1 k2} -> k1 ≡ k2 -> vis {A = A} e k1 wIT≈ vis e k

-- isEmbedding

helper-2 : ∀ {E} {R} -> (x : P₀ (itree E R)) -> out-fun (in-fun x) wITp≈ out-fun (in-fun x) ≡ x wITp≈ x
helper-2 = λ x i → out-inverse-in-x x i wITp≈ out-inverse-in-x x i

helper-3 : ∀ {E} {R} -> (x : itree E R) -> in-fun (out-fun x) wIT≈ in-fun (out-fun x) ≡ x wIT≈ x
helper-3 = λ x i → in-inverse-out-x x i wIT≈ in-inverse-out-x x i

helper-0 : ∀ {E} {R} -> ((x : P₀ (itree E R)) -> (in-fun x) wIT≈ (in-fun x)) -> ((x : P₀ (itree E R)) -> x wITp≈ x)
helper-0 f x = case f x return (λ _ → x wITp≈ x) of λ { (constr a b p) → transp (λ i -> helper-2 x i) i0 p }

helper-1 : ∀ {E} {R} -> ((x : P₀ (itree E R)) -> x wITp≈ x) -> ((x : P₀ (itree E R)) -> (in-fun x) wIT≈ (in-fun x))
helper-1 f x = constr (in-fun x) (in-fun x) (transp (λ i → sym (helper-2 x) i) i0 (f x))

helper-inverse : ∀ {E R} y -> helper-0 {E = E} {R = R} (helper-1 y) ≡ y
helper-inverse = λ y i x → transport⁻Transport (sym (helper-2 x)) (y x) i

helper : ∀ {E} {R} -> ((x : P₀ (itree E R)) -> (in-fun x) wIT≈ (in-fun x)) ≡ ((x : P₀ (itree E R)) -> x wITp≈ x)
helper {E} {R} i =
  -- isoToPath
  --   (iso ? ? ? ?)
  ua
    {A = (x : P₀ (itree E R)) → in-fun x wIT≈ in-fun x}
    {B = (x : P₀ (itree E R)) → x wITp≈ x}
    (helper-0 ,
     record {
       equiv-proof = λ y →
         (helper-1 y , helper-inverse y) , λ y₁ i₁ → {!!} , {!!} }) i 

-- mutual
--   weak-refl : ∀ {E} {R} (x : P₀ (itree E R)) -> x wITp≈ x
--   weak-refl {E} {R} (inl (inr r) , _) = EqRetP refl
--   weak-refl {E} {R} (inl (inl tt) , b) = EqTauP (weak-refl' (b (lift tt)))
--   weak-refl {E} {R} (inr (A , e) , _) = EqVisP refl 

--   weak-refl' : ∀ {E} {R} (x : itree E R) -> x wIT≈ x
--   weak-refl' x = weak-refl (out-fun x)


-- weak-refl : ∀ {E} {R} (x : itree E R) -> x wIT≈ x
-- weak-refl {E} {R} x =
--   case out-fun {S = itree-S E R} x return (λ _ -> x wIT≈ x) of
--     λ { (inl (inr r) , _) -> EqRet {r = r} {s = r} refl
--       ; (inl (inl tt) , b) -> EqTau (weak-refl (b (lift tt)))
--       ; (inr (A , e) , _) -> EqVis refl }

-- weak-refl (inl (inr r) , _) = EqRet refl
-- weak-refl (inl (inl tt) , b) = EqTau (weak-refl (b (lift tt)))
-- weak-refl (inr (A , e) , _) = EqVis refl

itree-Qw : ∀ {E} {R} -> itree E R -> QM (itree-S E R) _wIT≈_
itree-Qw = [_]

-- weak-equivalence-ex0 : ∀ {E} -> itree-Qw {E = E} (tau (ret 2)) ≡ itree-Qw (ret 2)
-- weak-equivalence-ex0 = eq/ (tau (ret 2)) (ret 2) (EqTauL (EqRet refl))

-- weak-equivalence-ex1 : ∀ {E R} (x : itree E R) -> itree-Qw {E = E} (tau x) ≡ itree-Qw x
-- weak-equivalence-ex1 x = eq/ (tau x) x (EqTauL ({!!} x))
