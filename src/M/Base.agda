{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat.Algebra

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun ; _∘_)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.FunExtEquiv
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.HLevels

open import Cubical.Foundations.Embedding

open import helper
open import Container
open import Coalg.Base

module M.Base where

--------------------------------
-- Limit of a Chain is Unique --
--------------------------------

open Iso

-- Lemma 12
L-unique-iso : ∀ {ℓ} -> {S : Container {ℓ}} -> Iso (L (shift-chain (sequence S))) (L (sequence S))
fun L-unique-iso (a , b) = (λ {0 → lift tt ; (suc n) → a n }) , λ { 0 → refl {x = lift tt} ; (suc n) → b n }
inv L-unique-iso (a , b) = a ∘ suc , b ∘ suc
fst (rightInv L-unique-iso (a , b) i) 0 = lift tt
fst (rightInv L-unique-iso (a , b) i) (suc n) = a (suc n)
snd (rightInv L-unique-iso (a , b) i) 0 = refl
snd (rightInv L-unique-iso (a , b) i) (suc n) = b (suc n)
leftInv L-unique-iso (a , b) = refl

PX,Pπ : ∀ {ℓ} (S : Container {ℓ}) -> Chain
PX,Pπ {ℓ} S =
  (λ n → P₀ {S = S} (X (sequence S) n)) ,,
  (λ {n : ℕ} x → P₁ (λ z → z) (π (sequence S) {n = suc n} x ))

--------------
-- Lemma 10 --
--------------

projection : ∀ {ℓ} {S : Container {ℓ}} n -> M S -> X (sequence S) n
projection n (x , q) = x n

β : ∀ {ℓ} {S : Container {ℓ}} -> (n : ℕ) → ∀ x → π (sequence S) {n = n} (projection (suc n) x) ≡ projection n x
β n (x , q) = q n

lemma10-Iso : ∀ {ℓ} {S : Container {ℓ}} {C,γ : Coalg₀ {S = S}} -> Iso (C,γ .fst -> M S) (Cone C,γ)
fun (lemma10-Iso) f = (λ n z → projection n (f z)) , λ n i a → β n (f a) i
inv (lemma10-Iso) (u , q) z = (λ n → u n z) , (λ n → funExt⁻ (q n) z)
rightInv (lemma10-Iso) = refl-fun
leftInv (lemma10-Iso) = refl-fun

------------------------------------
-- Shifting M-type is an equality --
------------------------------------

limit-collapse : ∀ {ℓ} {S : Container {ℓ}} (X : ℕ → Set ℓ) (l : (n : ℕ) → X n → X (suc n)) → (x₀ : X 0) → ∀ (n : ℕ) → X n
limit-collapse X l x₀ 0 = x₀
limit-collapse {S = S} X l x₀ (suc n) = l n (limit-collapse {S = S} X l x₀ n)

lemma11-Iso :
  ∀ {ℓ} {S : Container {ℓ}} (X : ℕ → Set ℓ) (l : (n : ℕ) → X n → X (suc n))
  → Iso (Σ ((n : ℕ) → X n) (λ x → (n : ℕ) → x (suc n) ≡ l n (x n)))
        (X 0)
fun (lemma11-Iso X l) (x , y) = x 0
inv (lemma11-Iso {S = S} X l) x₀ = limit-collapse {S = S} X l x₀ , (λ n → refl {x = limit-collapse {S = S} X l x₀ (suc n)})
rightInv (lemma11-Iso X l) = refl-fun
leftInv (lemma11-Iso {ℓ = ℓ} {S = S} X l) (x , y) i =
  let temp = χ-prop (x 0) (fst (inv (lemma11-Iso {S = S} X l) (fun (lemma11-Iso {S = S} X l) (x , y))) , refl , (λ n → refl {x = limit-collapse {S = S} X l (x 0) (suc n)})) (x , refl , y)
  in temp i .fst , proj₂ (temp i .snd)
  where
    open AlgebraPropositionality
    open NatSection
    open NatFiber

    X-fiber-over-ℕ : (x₀ : X 0) -> NatFiber NatAlgebraℕ ℓ
    Fiber (X-fiber-over-ℕ x₀) = X
    fib-zero (X-fiber-over-ℕ x₀) = x₀
    fib-suc (X-fiber-over-ℕ x₀) {n = n} = l n

    X-section : (x₀ : X 0) → (z : Σ ((n : ℕ) → X n) λ x → (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n))) -> NatSection (X-fiber-over-ℕ x₀)
    NatSection.section (X-section x₀ z) = fst z
    sec-comm-zero (X-section x₀ z) = proj₁ (snd z)
    sec-comm-suc (X-section x₀ z) = proj₂ (snd z)

    Z-is-Section : (x₀ : X 0) →
      Iso (Σ ((n : ℕ) → X n) λ x → (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)))
          (NatSection (X-fiber-over-ℕ x₀))
    fun (Z-is-Section x₀) (x , (z , y)) = record { section = x ; sec-comm-zero = z ; sec-comm-suc = y }
    inv (Z-is-Section x₀) x = NatSection.section x , (sec-comm-zero x , sec-comm-suc x)
    rightInv (Z-is-Section x₀) = refl-fun
    leftInv (Z-is-Section x₀) (x , (z , y)) = refl

    χ-prop' : (x₀ : X 0) → isProp (NatSection (X-fiber-over-ℕ x₀))
    χ-prop' x₀ a b = SectionProp.S≡T isNatInductiveℕ (X-section x₀ (inv (Z-is-Section x₀) a)) (X-section x₀ (inv (Z-is-Section x₀) b))

    χ-prop : (x₀ : X 0) → isProp (Σ ((n : ℕ) → X n) λ x → (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)))
    χ-prop x₀ = subst isProp (sym (isoToPath (Z-is-Section x₀))) (χ-prop' x₀)

α-iso-step-1-4-Iso : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso (L (PX,Pπ S))
        (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
            Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
               (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n)
                               (π (sequence S) ∘ u (suc n))
                               (u n))
fun (α-iso-step-1-4-Iso {S = S@(A , B)}) = (λ a → ((λ n → a .fst n .fst) , (λ n i → a .snd n i .fst)) , ((λ n → a .fst n .snd) , (λ n x₁ → a .snd n x₁ .snd)))
inv (α-iso-step-1-4-Iso {S = S@(A , B)}) = (λ a → (λ n → (a .fst .fst n) , (a .snd .fst n)) , (λ n i → a .fst .snd n i , a .snd .snd n i))
rightInv (α-iso-step-1-4-Iso {S = S@(A , B)}) = refl-fun
leftInv (α-iso-step-1-4-Iso {S = S@(A , B)}) = refl-fun

α-iso-step-5-Iso-helper0 :
  ∀ {ℓ} {S : Container {ℓ}}
  -> let (A , B) = S in (a : (ℕ -> A)) (p : (n : ℕ) → a (suc n) ≡ a n) (n : ℕ)
  -> a n ≡ a 0
α-iso-step-5-Iso-helper0 a p 0 = refl
α-iso-step-5-Iso-helper0 {S = S} a p (suc n) = p n ∙ α-iso-step-5-Iso-helper0 {S = S} a p n

α-iso-step-5-Iso-helper1 :
  ∀ {ℓ} {S : Container {ℓ}}
  -> let (A , B) = S in
  ∀ (a : ℕ -> A) (p : (n : ℕ) → a (suc n) ≡ a n) (u : (n : ℕ) → B (a n) → W S n) (n : ℕ) ->
    PathP (λ x → B (p n x) → W S n) (πₙ S ∘ u (suc n)) (u n)
      ≡
    (πₙ S ∘ (subst (\k -> B k → W (A , B) (suc n)) (α-iso-step-5-Iso-helper0 {S = S} a p (suc n))) (u (suc n)) ≡ subst (λ k → B k → W (A , B) n) (α-iso-step-5-Iso-helper0 {S = S} a p n) (u n))
α-iso-step-5-Iso-helper1 {S = S@(A , B)} a p u n =
  isoToPath (
  PathP (λ x → B (p n x) → W S n) (πₙ S ∘ u (suc n)) (u n)
    Iso⟨ pathToIso (PathP≡Path (λ x → B (p n x) → W S n) (πₙ S ∘ u (suc n)) (u n)) ⟩
  subst (λ k → B k → W S n) (p n) (πₙ S ∘ u (suc n)) ≡ (u n)
    Iso⟨ (sym-iso (≡-rel-a-inj-x-Iso (pathToIso (cong (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 a p n))))) ⟩
  (subst (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 {S = S} a p n) (subst (λ k → B k → W S n) (p n) (πₙ S ∘ u (suc n)))
      ≡
  subst (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 {S = S} a p n) (u n))
    Iso⟨ pathToIso (λ i → (sym (substComposite (λ k → B k → W S n) (p n) (α-iso-step-5-Iso-helper0 {S = S} a p n) (πₙ S ∘ u (suc n)))) i
                      ≡ subst (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 {S = S} a p n) (u n)) ⟩
  subst (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 {S = S} a p (suc n)) (πₙ S ∘ u (suc n))
    ≡
  subst (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 a p n) (u n)
    Iso⟨ pathToIso (λ i → (substCommSlice (λ k → B k → W S (suc n)) (λ k → B k → W S n) (λ a x x₁ → (πₙ S) (x x₁)) ((α-iso-step-5-Iso-helper0 {S = S} a p) (suc n)) (u (suc n))) i
            ≡ subst (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 {S = S} a p n) (u n)) ⟩
  πₙ S ∘ subst (λ k → B k → W S (suc n)) (α-iso-step-5-Iso-helper0 a p (suc n)) (u (suc n))
     ≡
  subst (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 {S = S} a p n) (u n) ∎Iso)

α-iso-step-5-Iso : ∀ {ℓ} {S : Container {ℓ}}
  -> let (A , B) = S in
  Iso
    (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
       Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
         (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
    (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
α-iso-step-5-Iso {S = S@(A , B)} =
  Σ-ap-iso (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) (λ a,p →
  Σ-ap-iso (pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → cong (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 {S = S} (a,p .fst) (a,p .snd) n)))) λ u →
           pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → α-iso-step-5-Iso-helper1 {S = S} (a,p .fst) (a,p .snd) u n)))

sym-α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso (Σ A (λ a → B a → M S))
        (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
sym-α-iso-step-6 {S = S@(A , B)} =
  Σ-ap-iso₂ λ x → lemma10-Iso {C,γ = B x , λ _ → x , (λ x₁ → x₁)}

-- -- Lemma 13
-- α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
-- α-iso {S = S@(A , B)} = isoToPath (compIso (α-iso-step-1-4-Iso) (compIso (α-iso-step-5-Iso) (sym-iso sym-α-iso-step-6)))

-----------------------------------------------------
-- Shifting the limit of a chain is an equivalence --
-----------------------------------------------------

comp-α-iso-step-1-4-Iso-Sym-L-unique-iso : ∀ {ℓ} {S : Container {ℓ}} -> let (A , B) = S in Iso (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))  (L (sequence S))
fun comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (a , b) = (λ { 0 → lift tt ; (suc n) → (a .fst n) , (b .fst n)}) , λ { 0 → refl {x = lift tt} ; (suc m) i → a .snd m i , b .snd m i }
inv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso x = ((λ n → (x .fst) (suc n) .fst) , λ n i → (x .snd) (suc n) i .fst) , (λ n → (x .fst) (suc n) .snd) , λ n i → (x .snd) (suc n) i .snd
fst (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) 0 = lift tt
fst (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) (suc n) = refl i
snd (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) 0 = refl
snd (rightInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (b , c) i) (suc n) = c (suc n)
leftInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso (a , b) = refl

shift-iso : ∀ {ℓ} {S : Container {ℓ}} -> Iso (P₀ {S = S} (M S)) (M S)
shift-iso {S = S@(A , B)} = (compIso sym-α-iso-step-6 (compIso (sym-iso (α-iso-step-5-Iso {S = S})) (comp-α-iso-step-1-4-Iso-Sym-L-unique-iso {S = S})))

shift : ∀ {ℓ} {S : Container {ℓ}} -> P₀ {S = S} (M S) ≡ M S
shift {S = S@(A , B)} = isoToPath shift-iso -- lemma 13 & lemma 12

-- Transporting along shift

in-fun : ∀ {ℓ} {S : Container {ℓ}} -> P₀ (M S) -> M S
in-fun {S = S} = fun (shift-iso {S = S})

out-fun : ∀ {ℓ} {S : Container {ℓ}} -> M S -> P₀ (M S)
out-fun {S = S} = inv (shift-iso {S = S})

----------------------------------------
-- Property of functions into M-types --
----------------------------------------

lift-to-M : ∀ {ℓ} {A : Set ℓ} {S : Container {ℓ}}
  → (x : (n : ℕ) -> A → X (sequence S) n)
  → ((n : ℕ) → (a : A) →  π (sequence S) (x (suc n) a) ≡ x n a)
  ---------------
  → (A → M S)
lift-to-M x p a = (λ n → x n a) , (λ n → p n a)

out-lift-to-M :
  ∀ {ℓ} {A : Set ℓ} {S : Container {ℓ}}
  → (lift-x : (n : ℕ) -> A → X (sequence S) n)
  → (lift-π : (n : ℕ) → (a : A) →  π (sequence S) (lift-x (suc n) a) ≡ lift-x n a)
  → (s : A)
  → out-fun (lift-to-M lift-x lift-π s)
  ≡ ((lift-x (suc 0) s .fst) , (λ z → (λ n → (subst (λ k → (n : ℕ) → k n) (funExt λ n → cong (λ k → S .snd k → W S n) (α-iso-step-5-Iso-helper0 {S = S} (λ n → lift-x (suc n) s .fst) ((λ n i → lift-π (suc n) s i .fst)) n)) (λ n → lift-x (suc n) s .snd)) n z) , (λ n → funExt⁻ ((subst (λ k → (n : ℕ) → k n) (funExt λ n → α-iso-step-5-Iso-helper1 (λ n → lift-x (suc n) s .fst) (λ n i → lift-π (suc n) s i .fst) (λ n → lift-x (suc n) s .snd) n) (λ n i → lift-π (suc n) s i .snd)) n) z)))
out-lift-to-M {S = S} lift-x lift-π s = refl

lift-direct-M : ∀ {ℓ} {S : Container {ℓ}}
  → (x : (n : ℕ) → X (sequence S) n)
  → ((n : ℕ) →  π (sequence S) (x (suc n)) ≡ x n)
  ---------------
  → M S
lift-direct-M x p = x , p
