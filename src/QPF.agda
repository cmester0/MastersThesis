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
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.helper

open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.HITs.SetQuotients renaming (elim to elim/)
open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥ ; rec to ∥rec∥ ; elim to ∥elim∥)

open import helper renaming (rec to rec/)

Quotient-Container : ∀ {ℓ} → (S : Container ℓ) → (R : {a : S .fst} → (Σ ((S .snd a) → (S .snd a) → Type ℓ) λ G → isEquiv G)) → Container ℓ
Quotient-Container (A , B) G = A , λ a → let (R , e) = G {a = a} in B a / R

F : ∀ {ℓ} → (S : Container ℓ) → (R : {a : S .fst} → (Σ ((S .snd a) → (S .snd a) → Type ℓ) λ G → isEquiv G)) → Type ℓ → Type ℓ
F S R = P₀ (Quotient-Container S R)

QPF₀ : ∀ {ℓ} → (S : Container ℓ) → ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ) → Type ℓ → Type ℓ
QPF₀ (A , B) R X = Σ[ a ∈ A ] ((B a → X) / R {a = a})

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

πₙ' : ∀ {ℓ} -> (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-as : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) -> {n : ℕ} -> Wₙ' S R (suc n) -> Wₙ' S R n
πₙ' _ _ _ {0} _ = lift tt
πₙ' S R R-as {suc n} = QPF₁ S R R-as (πₙ' S R R-as {n})

sequence' : ∀ {ℓ} -> (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-as : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) -> Chain ℓ
X (sequence' S R R-as) n = Wₙ' S R n
π (sequence' S R R-as) {n} = πₙ' S R R-as {n}

translate-x : ∀ {ℓ : Level} (S : Container ℓ) (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → ((n : ℕ) → Wₙ S n) → ((n : ℕ) → Wₙ' S R n)
translate-x S R p 0 = lift tt
translate-x S R p (suc n) = p (suc n) .fst , [ (λ _ → translate-x S R p n) ]

translate-π :
  ∀ {ℓ : Level} (S : Container ℓ) (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) (R-as : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y)))
  → {x : (n : ℕ) → Wₙ S n}
  → (p : (n : ℕ) → πₙ S (x (suc n)) ≡ x n)
  → (n : ℕ)
  → πₙ' S R R-as (translate-x S R x (suc n)) ≡ translate-x S R x n
translate-π S R R-as p 0 = refl
translate-π S R R-as {x} p (suc n) =
  πₙ' S R R-as (translate-x S R x (suc (suc n)))
    ≡⟨ refl ⟩
  x (suc (suc n)) .fst , [ (λ _ → πₙ' S R R-as (translate-x S R x (suc n))) ]
    ≡⟨ ΣPathP (cong fst (p (suc n)) , λ i → [ (λ v → translate-π S R R-as p n i) ]) ⟩
  x (suc n) .fst , [ (λ _ → translate-x S R x n) ]
    ≡⟨ refl ⟩
  translate-x S R x (suc n) ∎

QM : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-as : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → Type ℓ
QM S R R-as = limit-of-chain (sequence' S R R-as)

M→QM : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-as : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → M S → QM S R R-as
M→QM S R R-as m =
  (translate-x S R (m .fst)) ,
  (translate-π S R R-as {x = m .fst} (m .snd))

poly-quot : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-as : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → Set (ℓ-suc ℓ)
poly-quot {ℓ} S R R-as =
  Σ[ abs ∈ ({X : Set ℓ} → P₀ S X → QPF₀ S R X) ]
    ((∀ {X} → isSurjection (abs {X})) × ({X Y : Set ℓ} (f : X → Y) (x : P₀ S X) → abs (P₁ f x) ≡ QPF₁ S R R-as f (abs x))) -- Is one of these properties not enought?

poly-quot-constr : {ℓ : Level} (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-as : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → poly-quot S R R-as
poly-quot-constr S R R-as =
  (λ {(a , b) → a , [ b ]}) ,
  (λ {(a , b) → ∥map∥ (λ {(g , p) → (a , g) , ((a , [ g ]) ≡⟨ ΣPathP (refl , p) ⟩ (a , b) ∎)}) ([]surjective b) }) ,
  λ {f (a , b) → refl}

asdf : {ℓ : Level} (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-as : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → {!!}
asdf S R R-as =
  let temp = poly-quot-constr S R R-as in
  let temp' = M→QM in
    {!!}


-- -- Limit of chain
-- shift-iso' : ∀ {ℓ} (S : Container ℓ) (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) (R-as : ∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y)) → (∀ {a : S .fst} (x y : S .snd a → QM S R R-as) → R x y → x ≡ y) → (∀ n → isSet (Wₙ' S R n)) -> Iso (QPF₀ S R (QM S R R-as)) (QM S R R-as)
-- shift-iso' S@(A , B) R R-as R-bisim Wₙ'-isSet =
--   QPF₀ S R (QM S R R-as)
--     Iso⟨ Σ-ap-iso₂ (λ x → iso (λ f → rec/ (λ f' → (λ n z → f' z .fst n) , λ n i a → f' a .snd n i) (λ x y p → cong (λ v → (λ n z → v z .fst n) , λ n i a → v a .snd n i) (R-bisim x y p)) (isSetΣ (isSetΠ λ n → isSetΠ λ _ → Wₙ'-isSet n) λ _ → isSetΠ λ n → isSet→isGroupoid (isSetΠ (λ _ → Wₙ'-isSet n)) _ _) f)
--                                (λ {(u , q) → [ (λ z → (λ n → u n z) , λ n i → q n i z) ]})
--                                (λ _ → refl)
--                                {!!}) ⟩
--   (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → B a → Wₙ' S R n) ] ((n : ℕ) → πₙ' S R R-as ∘ {!!} ≡ u n))) -- (λ x → ∥map∥ (πₙ' S R R-as) (u (suc n) x)) ≡ u n
--   -- let temp = rec/ (λ f' → f' a .snd n i) (λ x y p → cong (λ z → z a .snd n i) (R-bisim x y p)) (Wₙ'-isSet n) f in
--     --   Iso⟨ Σ-ap-iso₂ (λ x → iso (λ f → (λ n z → f z .fst n) , λ n i a → f a .snd n i)
--   --                              (λ (u , q) z → (λ n → u n z) , λ n i → q n i z)
--   --                             (λ _ → refl)
--   --                             (λ _ → refl)) ⟩
--   -- (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → B a → Wₙ' S n) ] ((n : ℕ) → πₙ' S R R-as ∘ (u (suc n)) ≡ u n)))
--   --   Iso⟨ invIso α-iso-step-5-Iso ⟩
--   -- (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
--   --       Σ[ u ∈ ((n : ℕ) → B (a .fst n) → Wₙ' S n) ]
--   --          ((n : ℕ) → PathP (λ x → B (a .snd n x) → Wₙ' S n)
--   --                              (πₙ' S R R-as ∘ u (suc n))
--   --                              (u n)))
--   -- Iso⟨ α-iso-step-1-4-Iso-lem-12 ⟩
--     Iso⟨ {!!} ⟩
--   QM S R R-as ∎Iso
--     where
--       open Iso
      
--       α-iso-step-5-Iso-helper0 :
--         ∀ (a : (ℕ -> A))
--         → (p : (n : ℕ) → a (suc n) ≡ a n)
--         → (n : ℕ)
--         → a n ≡ a 0
--       α-iso-step-5-Iso-helper0 a p 0 = refl
--       α-iso-step-5-Iso-helper0 a p (suc n) = p n ∙ α-iso-step-5-Iso-helper0 a p n

--       α-iso-step-5-Iso-helper1-Iso :
--         ∀ (a : ℕ -> A)
--         → (p : (n : ℕ) → a (suc n) ≡ a n)
--         → (u : (n : ℕ) → B (a n) → Wₙ' S R n)
--         → (n : ℕ)
--         → Iso
--             (PathP (λ x → B (p n x) → Wₙ' S R n) (πₙ' S R R-as ∘ u (suc n)) (u n))
--             (πₙ' S R R-as ∘ (subst (\k -> B k → Wₙ' S R (suc n)) (α-iso-step-5-Iso-helper0 a p (suc n))) (u (suc n)) ≡ subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a p n) (u n))
--       α-iso-step-5-Iso-helper1-Iso  a p u n  =
--         PathP (λ x → B (p n x) → Wₙ' S R n) (πₙ' S R R-as ∘ u (suc n)) (u n)
--           Iso⟨ pathToIso (PathP≡Path (λ x → B (p n x) → Wₙ' S R n) (πₙ' S R R-as ∘ u (suc n)) (u n)) ⟩
--         subst (λ k → B k → Wₙ' S R n) (p n) (πₙ' S R R-as ∘ u (suc n)) ≡ (u n)
--           Iso⟨ (invIso (temp (pathToIso (cong (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a p n))))) ⟩
--         (subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a p n) (subst (λ k → B k → Wₙ' S R n) (p n) (πₙ' S R R-as ∘ u (suc n)))
--                ≡
--         subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a p n) (u n))
--           Iso⟨ pathToIso (λ i → (sym (substComposite (λ k → B k → Wₙ' S R n) (p n) (α-iso-step-5-Iso-helper0 a p n) (πₙ' S R R-as ∘ u (suc n)))) i
--                             ≡ subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a p n) (u n)) ⟩
--         subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a p (suc n)) (πₙ' S R R-as ∘ u (suc n))
--           ≡
--         subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a p n) (u n)
--           Iso⟨ pathToIso (λ i → (substCommSlice (λ k → B k → Wₙ' S R (suc n)) (λ k → B k → Wₙ' S R n) (λ a x x₁ → (πₙ' S R R-as) (x x₁)) ((α-iso-step-5-Iso-helper0 a p) (suc n)) (u (suc n))) i
--                          ≡ subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a p n) (u n)) ⟩
--         πₙ' S R R-as ∘ subst (λ k → B k → Wₙ' S R (suc n)) (α-iso-step-5-Iso-helper0 a p (suc n)) (u (suc n))
--           ≡
--         subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a p n) (u n) ∎Iso
--         where
--           abstract
--             temp = iso→fun-Injection-Iso-x

--       α-iso-step-5-Iso :
--         Iso
--           (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
--             Σ[ u ∈ ((n : ℕ) → B (a .fst n) → Wₙ' S R n) ]
--               ((n : ℕ) → PathP (λ x → B (a .snd n x) → Wₙ' S R n)
--                                   (πₙ' S R R-as ∘ u (suc n))
--                                   (u n)))
--             (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → B a → Wₙ' S R n) ] ((n : ℕ) → πₙ' S R R-as ∘ (u (suc n)) ≡ u n)))
--       α-iso-step-5-Iso =
--         Σ-ap-iso (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) (λ a,p →
--           Σ-ap-iso (pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → cong (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 (a,p .fst) (a,p .snd) n)))) λ u →
--                               pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → isoToPath (α-iso-step-5-Iso-helper1-Iso (a,p .fst) (a,p .snd) u n))))

--       α-iso-step-1-4-Iso-lem-12 :
--         Iso (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A)] ((n : ℕ) → a (suc n) ≡ a n)) ]
--                   (Σ[ u ∈ ((n : ℕ) → B (a .fst n) → Wₙ' S R n) ]
--                       ((n : ℕ) → PathP (λ x → B (a .snd n x) → Wₙ' S R n)
--                                           (πₙ' S R R-as ∘ u (suc n))
--                                           (u n))))
--             (QM S R R-as)
--       α-iso-step-1-4-Iso-lem-12 = {!!}
--       -- fun α-iso-step-1-4-Iso-lem-12 (a , b) = (λ { 0 → lift tt ; (suc n) → (a .fst n) , (b .fst n)}) , λ { 0 → refl {x = lift tt} ; (suc m) i → a .snd m i , b .snd m i }
--       -- inv α-iso-step-1-4-Iso-lem-12 x = ((λ n → (x .fst) (suc n) .fst) , λ n i → (x .snd) (suc n) i .fst) , (λ n → (x .fst) (suc n) .snd) , λ n i → (x .snd) (suc n) i .snd
--       -- fst (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) 0 = lift tt
--       -- fst (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) (suc n) = refl i
--       -- snd (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) 0 = refl
--       -- snd (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) (suc n) = c (suc n)
--       -- leftInv α-iso-step-1-4-Iso-lem-12 (a , b) = refl

