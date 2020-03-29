{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma

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

open import Cubical.Data.Sum

open import helper
open import Container

open import Coalg.Base

module M.Base where

--------------------------------
-- Limit of a Chain is Unique --
--------------------------------

open Iso

postulate
  lemma11-Iso : ∀ {ℓ} {S : Container {ℓ}} (X : ℕ → Set ℓ) (l : (n : ℕ) → X n → X (suc n)) → Iso (Σ ((n : ℕ) → X n) (λ x → (n : ℕ) → x (suc n) ≡ l n (x n))) (X 0)
  lemma11 : ∀ {ℓ} {S : Container {ℓ}} (X : ℕ → Set ℓ) (l : (n : ℕ) → X n → X (suc n)) → Σ ((n : ℕ) → X n) (λ x → (n : ℕ) → x (suc n) ≡ l n (x n)) ≡ X 0
  lemma11-2 : ∀ {ℓ} {S : Container {ℓ}} a p n → a n ≡ transport (lemma11 {S = S} (λ _ → S .fst) (λ _ x₂ → x₂)) (a , p) 
  lemma11-2-Iso : ∀ {ℓ} {S : Container {ℓ}} a p n → a n ≡ fun (lemma11-Iso {S = S} (λ _ → S .fst) (λ _ x₂ → x₂)) (a , p)
  
-- -- helper
-- eight-nine :
--   ∀ {ℓ} -> {S : Container {ℓ}} →
--   let (A , B) = S in
--   Σ ((n : ℕ) → A) (λ a → Σ ((n : ℕ) → a (suc n) ≡ a n) λ p → Σ ((n : ℕ) → B (a n) → X (sequence S) n) λ u → (n : ℕ) → transport (λ i → B (p n i) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) ≡ u n)
--   ≡
--   Σ A λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ u (suc n) ≡ u n
-- eight-nine {S = S@(A , B)} =
--   Σ ((n : ℕ) → A) (λ a → Σ ((n : ℕ) → a (suc n) ≡ a n) λ p → Σ ((n : ℕ) → B (a n) → X (sequence S) n) λ u → (n : ℕ) → transport (λ i → B (p n i) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) ≡ u n)
--     ≡⟨ isoToPath (iso (λ {(a , (b , (c , d))) → (a , b) , (c , d)}) (λ {((a , b) , (c , d)) → a , (b , (c , d))}) refl-fun refl-fun) ⟩
--   Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) (λ ap →
--     Σ ((n : ℕ) → B (ap .fst n) → X (sequence S) n) λ u → (n : ℕ) → transport (λ i → B (ap .snd n i) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) ≡ u n)
--     ≡⟨ Σ-ap (lemma11 {S = S} (λ _ → A) λ _ x → x) (λ {(a , p) → {!!}}) ⟩
--   (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ u (suc n) ≡ u n)) ∎

-- isoToPath (iso (λ {(x , y) → (λ n x₁ → x n (subst B (lemma11-2 a p n) x₁)) , λ n i a₁ → {!!}})
--                                                                                   (λ {(x , y) → (λ n x₁ → x n (subst B (sym (lemma11-2 a p n)) x₁)) , {!!}})
--                                                                                   {!!}
--                                                                                   {!!})

-- Lemma 12
L-unique-iso : ∀ {ℓ} -> {S : Container {ℓ}} -> Iso (L (shift-chain (sequence S))) (L (sequence S))
fun L-unique-iso (a , b) = (λ {0 → lift tt ; (suc n) → a n }) , λ { 0 → refl {x = lift tt} ; (suc n) → b n }
inv L-unique-iso x = x .fst ∘ suc , x .snd ∘ suc
fst (rightInv L-unique-iso (a , b) i) 0 = lift tt
fst (rightInv L-unique-iso (a , b) i) (suc n) = a (suc n)
snd (rightInv L-unique-iso (a , b) i) 0 = refl
snd (rightInv L-unique-iso (a , b) i) (suc n) = b (suc n)
leftInv L-unique-iso x = ΣPathP (refl , refl)

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
inv (lemma10-Iso) (u , q) z = (λ n → u n z) , λ n i → q n i z
rightInv (lemma10-Iso) = refl-fun
leftInv (lemma10-Iso) = refl-fun

lemma10 : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ .fst -> M S) ≡ Cone C,γ
lemma10 {S = S} C,γ@(C , γ) = isoToPath (lemma10-Iso {C,γ = C,γ})

------------------------------------
-- Shifting M-type is an equality --
------------------------------------

swap-Σ-∀-Iso :
  ∀ {ℓ} (X : ℕ -> Set ℓ)
    -> (A : Set ℓ)
    -> (B : A -> Set ℓ)
    -> (p : {n : ℕ} -> Σ A (λ a -> B a -> X (suc n)) -> Σ A (λ a -> B a -> X n) -> Set ℓ)
    -----------------------
    -> Iso (Σ (∀ (n : ℕ) -> Σ A (λ a -> B a -> X n)) (λ w -> (n : ℕ) -> p (w (suc n)) (w n)))
           (Σ ((n : ℕ) → A) λ a → Σ ((n : ℕ) → B (a n) → X n) λ u → (n : ℕ) -> p (a (suc n) , u (suc n)) (a n , u n))
fun (swap-Σ-∀-Iso X A B p) = (λ {(x , y) → (λ n → x n .fst) , (λ n → x n .snd) , y})
inv (swap-Σ-∀-Iso X A B p) = (λ {(x , (y , z)) → (λ n → (x n) , y n) , z})
rightInv (swap-Σ-∀-Iso X A B p) = refl-fun
leftInv (swap-Σ-∀-Iso X A B p) = refl-fun

swap-Σ-∀ :
  ∀ {ℓ} (X : ℕ -> Set ℓ)
    -> (A : Set ℓ)
    -> (B : A -> Set ℓ)
    -> (p : {n : ℕ} -> Σ A (λ a -> B a -> X (suc n)) -> Σ A (λ a -> B a -> X n) -> Set ℓ)
    -----------------------
    -> (Σ (∀ (n : ℕ) -> Σ A (λ a -> B a -> X n)) (λ w -> (n : ℕ) -> p (w (suc n)) (w n)))
    ≡ (Σ ((n : ℕ) → A) λ a → Σ ((n : ℕ) → B (a n) → X n) λ u → (n : ℕ) -> p (a (suc n) , u (suc n)) (a n , u n))
swap-Σ-∀ X A B p = isoToPath (swap-Σ-∀-Iso X A B p)

contr-⊤-iso-Iso : ∀ {i} {X : Set i} → (isContr X) → Iso X (Lift {ℓ-zero} {i} Unit)
fun (contr-⊤-iso-Iso hX) = (λ _ → lift tt)
inv (contr-⊤-iso-Iso hX) = (λ _ → fst hX)
rightInv (contr-⊤-iso-Iso hX) = (λ {(lift tt) → refl})
leftInv (contr-⊤-iso-Iso hX) = λ a → snd hX a

contr-⊤-iso : ∀ {i}{X : Set i} → isContr X → X ≡ Lift Unit
contr-⊤-iso = isoToPath ∘ contr-⊤-iso-Iso

lemma11-helper-Iso :
  ∀ {ℓ} {S : Container {ℓ}}
  → (χ : (x₀ : X (sequence S) 0)
       → isContr ( Σ ((n : ℕ) → X (sequence S) n) λ x
       → (x₀ ≡ x 0)
       × (∀ n → π (sequence S) (x (suc n)) ≡ x n) ) )
  → Iso (M S) (X (sequence S) 0)
lemma11-helper-Iso {ℓ} {S = S} χ =
  M S
    Iso⟨ Σ-ap-iso₂ (λ x → sym-iso (∏-ap-iso refl-iso λ n → refl)) ⟩
  Σ ((n : ℕ) → X (sequence S) n) (λ x → (n : ℕ) →
   π (sequence S) (x (suc n)) ≡ x n)
    Iso⟨ Σ-ap-iso₂ (λ x → iso (λ x₁ → lift {ℓ-zero} {ℓ} tt , x₁) (λ x₁ → x₁ .snd) refl-fun refl-fun) ⟩
  Σ ((n : ℕ) → X (sequence S) n) (λ x →
  Σ (Lift Unit) λ _ → (n : ℕ) →
   π (sequence S) (x (suc n)) ≡ x n)
    Iso⟨  Σ-ap-iso₂ (λ x →
          Σ-ap-iso (iso (λ x₁ → (lift tt) , (λ i → lift tt)) (λ x₁ → lift tt) (λ {(a , b) → λ _ → (lift tt) , (λ _ → lift tt)}) λ a → refl) λ _ → refl-iso) ⟩
  Σ ((n : ℕ) → X (sequence S) n) (λ x →
  Σ (singl (x 0)) λ _ → (n : ℕ) →
   π (sequence S) (x (suc n)) ≡ x n)
    Iso⟨ iso (λ { (x , (z , p) , q) → z , x , p , q })
             (λ { (lift tt , x , p , q) → x , ((lift tt) , p) , q })
             (λ { (lift tt , x , p , q) → refl })
             (λ { (x , (lift tt , p) , q) → refl {x = x , (((lift tt) , p) , q)} }) ⟩
  Σ (X (sequence S) 0) (λ z →
  Σ ((n : ℕ) → X (sequence S) n) λ x →
  Σ (z ≡ x 0) λ _ → (n : ℕ) →
   π (sequence S) (x (suc n)) ≡ x n)
    Iso⟨ (Σ-ap-iso₂ λ z → case χ z of λ {((a , (b , c)) , d) →
         contr-⊤-iso-Iso ((a , b , c) , λ {(y , w , v) i → case d (y , w , v) i of λ {(α , β , γ) → α , β , γ }})}) ⟩
  Σ (X (sequence S) 0) (λ z → Lift Unit)
    Iso⟨ (iso (λ _ → lift tt) (λ _ → lift tt , lift tt) refl-fun refl-fun) ⟩
  X (sequence S) 0 ∎Iso

lemma11-helper :
  ∀ {ℓ} {S : Container {ℓ}}
  → (χ : (x₀ : X (sequence S) 0)
        → isContr ( Σ ((n : ℕ) → X (sequence S) n) λ x
        → (x₀ ≡ x 0)
        × (∀ n → π (sequence S) (x (suc n)) ≡ x n) ) )
  → M S ≡ X (sequence S) 0
lemma11-helper = isoToPath ∘ lemma11-helper-Iso

-- postulate
--   lemma11 : ∀ {ℓ} {S : Container {ℓ}} -> M S ≡ X (sequence S) 0

α-iso-step-1-4-Iso : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso (L (PX,Pπ S))
        (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a → Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
fun (α-iso-step-1-4-Iso {S = S@(A , B)}) = (λ a → ((λ n → a .fst n .fst) , (λ n i → a .snd n i .fst)) , ((λ n → a .fst n .snd) , (λ n x₁ → a .snd n x₁ .snd)))
inv (α-iso-step-1-4-Iso {S = S@(A , B)}) = (λ a → (λ n → (a .fst .fst n) , (a .snd .fst n)) , (λ n i → a .fst .snd n i , a .snd .snd n i))
rightInv (α-iso-step-1-4-Iso {S = S@(A , B)}) = refl-fun
leftInv (α-iso-step-1-4-Iso {S = S@(A , B)}) = refl-fun

α-iso-step-1-4 : ∀ {ℓ} {S : Container {ℓ}}
    → L (PX,Pπ S)
    ≡ let (A , B) = S in
       (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
        Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u → (n : ℕ) →
          PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
α-iso-step-1-4 {S = S@(A , B)} = isoToPath α-iso-step-1-4-Iso

α-iso-step-5'-Iso : ∀ {ℓ} {S : Container {ℓ}}
  -> let (A , B) = S in
  Iso
    (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
      Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
        (n : ℕ) → transport (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) ≡ (u n))
    (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
α-iso-step-5'-Iso {S = S@(A , B)} =
  (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
     Σ ((n : ℕ) → B (a .fst n) → W S n) λ u →
       (n : ℕ) → transport (λ x → B (a .snd n x) → W S n) (πₙ S ∘ u (suc n)) ≡ (u n))
    Iso⟨ Σ-ap-iso ((lemma11-Iso {S = S} (λ _ → A) λ _ x → x)) (λ {(a , p) →
       Σ-ap-iso (pathToIso (lemma11-temp (a , p))) (λ x → pathToIso (cong (λ k → (n : ℕ) → k n) (funExt (lemma11-temp-2 (a , p) x))))}) ⟩
  (Σ A λ a → Σ ((n : ℕ) → B a → W S n) λ u →
     (n : ℕ) → transport (λ x → B a → W S n) (πₙ S ∘ u (suc n)) ≡ (u n))
    Iso⟨ Σ-ap-iso₂ (λ a → Σ-ap-iso₂ λ u → pathToIso (cong (λ k → (n : ℕ) → k n ≡ u n) (funExt λ n → transportRefl (πₙ S ∘ u (suc n))))) ⟩
  Σ A (λ a → Σ ((n : ℕ) → B a → W S n) λ u →
     (n : ℕ) → πₙ S ∘ u (suc n) ≡ u n) ∎Iso
    where
      lemma11-temp :
          (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
          ((n : ℕ) → B (a .fst n) → W (A , B) n) ≡
          ((n : ℕ) → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) a) → W (A , B) n)
      lemma11-temp a =
        (cong (λ k → (n : ℕ) → B (k n) → W S n) (funExt (lemma11-2-Iso (a .fst) (a .snd))))

      postulate
        lemma11-temp-2 :
          (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
          (x : (n : ℕ) → B (a .fst n) → W (A , B) n) →
          (n : ℕ) → 
          (transport (λ x₁ → B (a .snd n x₁) → W (A , B) n)
                               (λ x₁ → πₙ (A , B) (x (suc n) x₁))
                     ≡ x n)
          ≡
          (transport (λ x₁ → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x₂ → x₂)) a) → W (A , B) n)
                               (λ x₁ → πₙ (A , B) (transport (lemma11-temp a) x (suc n) x₁))
                     ≡ transport (lemma11-temp a) x n)

sym-α-iso-step-5-Iso : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso
      (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
      (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
        Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
          (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
sym-α-iso-step-5-Iso {S = S@(A , B)} =
  Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ u (suc n) ≡ u n)
    Iso⟨ sym-iso α-iso-step-5'-Iso ⟩
  (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
     Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
       (n : ℕ) → transport (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) ≡ (u n))
    Iso⟨ iso (λ {((x , y) , (z , w)) → (x , y) , (z , λ n → transport⁻ (PathP≡Path (λ x → B (y n x) → X (sequence S) n) (πₙ S ∘ z (suc n)) (z n)) (w n))})
             (λ {((x , y) , (z , w)) → (x , y) , (z , λ n → transport (PathP≡Path (λ x → B (y n x) → X (sequence S) n) (πₙ S ∘ z (suc n)) (z n)) (w n))})
             (λ {((x , y) , (z , w)) → λ i → (x , y) , (z , (λ n → transport⁻Transport (PathP≡Path (λ x → B (y n x) → X (sequence S) n) (πₙ S ∘ z (suc n)) (z n)) (w n) i))})
             (λ {((x , y) , (z , w)) → λ i → (x , y) , (z , (λ n → transportTransport⁻ (PathP≡Path (λ x → B (y n x) → X (sequence S) n) (πₙ S ∘ z (suc n)) (z n)) (w n) i))}) ⟩
  (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) (λ a →
     Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
       (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))) ∎Iso

α-iso-step-5 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
      Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
        (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
    ≡ Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
α-iso-step-5 {S = S@(A , B)} = isoToPath (sym-iso sym-α-iso-step-5-Iso)

sym-α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso (Σ A (λ a → B a → M S))
        (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
fun (sym-α-iso-step-6 {S = S@(A , B)}) (x , y') = x , transport (lemma10 (B x , λ _ → x , (λ x₁ → x₁))) y'
inv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y) = x , transport (sym (lemma10 (B x , λ _ → x , (λ x₁ → x₁)))) y
rightInv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y') = ΣPathP (refl {x = x} , transport⁻Transport (sym (lemma10 (B x , λ _ → x , (λ x₁ → x₁)))) y')
leftInv (sym-α-iso-step-6 {S = S@(A , B)}) (x , y) = ΣPathP (refl {x = x} , transportTransport⁻ (sym (lemma10 (B x , λ _ → x , (λ x₁ → x₁)))) y)

α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)
    ≡ Σ A (λ a → B a → M S)
α-iso-step-6 {S = S@(A , B)} = Σ-ap₂ (λ a i → lemma10 (B a , (λ x → a , (λ x₁ → x₁))) (~ i))

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
α-iso {S = S@(A , B)} =
  α-iso-step-1-4 □ (α-iso-step-5 □ α-iso-step-6)

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
leftInv comp-α-iso-step-1-4-Iso-Sym-L-unique-iso a = ΣPathP (refl , refl)

shift-iso : ∀ {ℓ} {S : Container {ℓ}} -> Iso (P₀ {S = S} (M S)) (M S)
shift-iso {S = S@(A , B)} = (compIso (sym-α-iso-step-6) (compIso (sym-α-iso-step-5-Iso {S = S}) (comp-α-iso-step-1-4-Iso-Sym-L-unique-iso {S = S})))

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
lift-to-M x p a = (λ n → x n a) , λ n i → p n a i

lift-direct-M : ∀ {ℓ} {S : Container {ℓ}}
  → (x : (n : ℕ) → X (sequence S) n)
  → ((n : ℕ) →  π (sequence S) (x (suc n)) ≡ x n)
  ---------------
  → M S
lift-direct-M x p = x , p
