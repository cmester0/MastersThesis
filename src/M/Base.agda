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
inv (lemma10-Iso) (u , q) z = (λ n → u n z) , λ n i → q n i z
rightInv (lemma10-Iso) = refl-fun
leftInv (lemma10-Iso) = refl-fun

-- lemma10 : ∀ {ℓ} {S : Container {ℓ}} (C,γ : Coalg₀ {S = S}) -> (C,γ .fst -> M S) ≡ Cone C,γ
-- lemma10 {S = S} C,γ@(C , γ) = isoToPath (lemma10-Iso {C,γ = C,γ})

------------------------------------
-- Shifting M-type is an equality --
------------------------------------

contr-⊤-iso : ∀ {i} {X : Set i} → (isContr X) → Iso X (Lift {ℓ-zero} {i} Unit)
fun (contr-⊤-iso hX) = (λ _ → lift tt)
inv (contr-⊤-iso hX) = (λ _ → fst hX)
rightInv (contr-⊤-iso hX) = (λ {(lift tt) → refl})
leftInv (contr-⊤-iso hX) = λ a → snd hX a

singl-contr : ∀ {i} {A : Set i} → (x : A) → isContr (singl x)
singl-contr {A = A} x = (x , refl) , λ { (x' , p) → contrSingl p }

lemma11-Iso :
  ∀ {ℓ} {S : Container {ℓ}} (X : ℕ → Set ℓ) (l : (n : ℕ) → X n → X (suc n))
  → Iso (Σ ((n : ℕ) → X n) (λ x → (n : ℕ) → x (suc n) ≡ l n (x n)))
         (X 0)
lemma11-Iso {ℓ = ℓ} {S = S} X l =
  Σ ((n : ℕ) → X n) (λ x → (n : ℕ) → x (suc n) ≡ l n (x n))
    Iso⟨ iso (λ x → (x .fst) , ((lift tt) , (x .snd))) (λ x → (x .fst) , x .snd .snd) refl-fun refl-fun ⟩
  Σ ((n : ℕ) → X n) (λ x →
  Σ (Lift Unit) (λ _ →
    (n : ℕ) → x (suc n) ≡ l n (x n)))
    Iso⟨ Σ-ap-iso₂ (λ x → Σ-ap-iso (sym-iso (contr-⊤-iso (singl-contr (x 0)))) λ x₁ → refl-iso) ⟩
  Σ ((n : ℕ) → X n) (λ x →
  Σ (singl (x 0)) (λ _ →
    (n : ℕ) → x (suc n) ≡ l n (x n)))
    Iso⟨ iso (λ {(x , (z , p) , q) → (z , x , p , q)})
             (λ {(z , x , p , q) → (x , (z , p) , q)})
             (λ {(z , x , p , q) → refl})
             refl-fun ⟩
  (Σ (X 0) (λ z -> Σ ((n : ℕ) → X n) (λ x → (x 0 ≡ z) × ((n : ℕ) → x (suc n) ≡ l n (x n)))))
    Iso⟨ {!!} ⟩  
    -- Iso⟨ Σ-ap-iso₂ (λ z → contr-⊤-iso (χ z))⟩
  -- (Σ (X 0) (λ z -> Lift Unit))
  --   Iso⟨ iso (λ x → x .fst) (λ x → x , (lift tt)) refl-fun refl-fun ⟩
  X 0 ∎Iso
  where
    open AlgebraPropositionality
    open NatSection    

    temp' : (x₀ : X 0) -> NatFiber NatAlgebraℕ ℓ
    temp' x₀ = record { Fiber = X ; fib-zero = x₀ ; fib-suc = λ {n : ℕ} xₙ → l n xₙ }

    temp : (x₀ : X 0) → (z : Σ ((n : ℕ) → X n) λ x → (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n))) -> NatSection (temp' x₀)
    temp = λ x₀ z → record { section = fst z ; sec-comm-zero = proj₁ (snd z) ; sec-comm-suc = proj₂ (snd z) }

    helper : (x₀ : X 0) →
      Iso (Σ ((n : ℕ) → X n) λ x → (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)))
          (NatSection (temp' x₀))
    fun (helper x₀) (x , (z , y)) = record { section = x ; sec-comm-zero = z ; sec-comm-suc = y }
    inv (helper x₀) x = NatSection.section x , (sec-comm-zero x , sec-comm-suc x)
    rightInv (helper x₀) = refl-fun
    leftInv (helper x₀) (x , (z , y)) = refl

    helper' : (x₀ : X 0)
      → (Σ ((n : ℕ) → X n) λ x → (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)))
      ≡ (NatSection (temp' x₀))
    helper' x₀ = isoToPath (helper x₀)

    -- S≡T
    χ-prop' : (x₀ : X 0) → isProp (NatSection (temp' x₀))
    χ-prop' x₀ a b = SectionProp.S≡T isNatInductiveℕ (temp x₀ (inv (helper x₀) a)) (temp x₀ (inv (helper x₀) b))

    asdfafds : ∀ A B (k : A ≡ B) → isProp (k i0) ≡ isProp (k i1)
    asdfafds A B k = λ i → isProp (k i)

    χ-prop : (x₀ : X 0) → isProp (Σ ((n : ℕ) → X n) λ x → (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)))
    χ-prop x₀ =
      transport (asdfafds (NatSection (temp' x₀))
                          (Σ ((n : ℕ) → X n) (λ x → (x 0 ≡ x₀) × (∀ n → x (suc n) ≡ l n (x n))))
                             (sym (helper' x₀))) (χ-prop' x₀)

    χ : (x₀ : X 0) → isContr ( Σ ((n : ℕ) → X n) λ x → (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)) )
    χ x₀ = {!!} -- isNatHInitial -- isContrΣ

-- Same as leftInv1'
lemma11-2-Iso : ∀ {ℓ} {S : Container {ℓ}} a p n → a n ≡ fun (lemma11-Iso {S = S} (λ _ → S .fst) (λ _ x₂ → x₂)) (a , p) -- = a 0
lemma11-2-Iso a p 0 = refl
lemma11-2-Iso {S = S} a p (suc n) = p n ∙ lemma11-2-Iso {S = S} a p n
  
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

-- α-iso-step-5'-Iso : ∀ {ℓ} {S : Container {ℓ}}
--     -> let (A , B) = S in
--     Iso
--       (Σ (L ((λ _ → A) ,, λ x → x)) λ a →
--         Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
--           (n : ℕ) → transport (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) ≡ (u n))
--       (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
-- α-iso-step-5'-Iso {S = S@(A , B)} =
--   (Σ (L ((λ _ → A) ,, λ x → x)) λ a →
--      Σ ((n : ℕ) → B (a .fst n) → W S n) λ u →
--        (n : ℕ) → transport (λ x → B (a .snd n x) → W S n) (πₙ S ∘ u (suc n)) ≡ (u n))
--     Iso⟨ Σ-ap-iso (lemma11-Iso {S = S} (λ _ → A) λ _ x → x) (λ {(a , p) →
--        Σ-ap-iso (lemma11-temp (a , p)) (lemma11-temp-2-ext (a , p))}) ⟩
--   (Σ A λ a → Σ ((n : ℕ) → B a → W S n) λ u →
--      (n : ℕ) → transport (λ x → B a → W S n) (πₙ S ∘ u (suc n)) ≡ (u n))
--     Iso⟨ Σ-ap-iso₂ (λ a → Σ-ap-iso₂ λ u →
--          iso (λ x n → subst (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n)))) (x n))
--              (λ x n → subst (λ k → k n ≡ u n) (sym (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))) (x n))
--              (λ b i n → transportTransport⁻ (cong (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))) (b n) i)
--              (λ b i n → transport⁻Transport (cong (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))) (b n) i)) ⟩
--   Σ A (λ a → Σ ((n : ℕ) → B a → W S n) λ u →
--      (n : ℕ) → πₙ S ∘ u (suc n) ≡ u n) ∎Iso
--     where
--       lemma11-temp-Path :
--         (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n))
--         → ((n : ℕ) → B (a .fst n) → W (A , B) n)
--         ≡ ((n : ℕ) → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) a) → W (A , B) n)
--       lemma11-temp-Path a = cong (λ k → (n : ℕ) → k n) (funExt λ n → λ i → B (lemma11-2-Iso {S = S} (a .fst) (a .snd) n i) → W (A , B) n)

--       lemma11-temp :
--         (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
--           Iso
--             ((n : ℕ) → B (a .fst n) → W (A , B) n)
--             ((n : ℕ) → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) a) → W (A , B) n)
--       lemma11-temp = pathToIso ∘ lemma11-temp-Path 

--       postulate
--         lemma11-temp-2 :
--           (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
--           (x : (n : ℕ) → B (a .fst n) → W (A , B) n) →
--           (n : ℕ) →
--           Iso
--             (subst (λ x₁ → B x₁ → W (A , B) n)
--                    (a .snd n)
--                    (λ x₁ → πₙ (A , B) (x (suc n) x₁))
--               ≡ x n)
--             (subst (λ x₁ → B x₁ → W (A , B) n)
--                    (\ _ -> fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x₂ → x₂)) a)
--                    (λ x₁ → πₙ (A , B) (fun (lemma11-temp a) x (suc n) x₁))
--               ≡ fun (lemma11-temp a) x n)
      
--       lemma11-temp-2-ext :
--           (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
--           (x : (n : ℕ) → B (a .fst n) → W (A , B) n) →
--           Iso
--             ((n : ℕ) → transport (λ x₁ → B (snd a n x₁) → W (A , B) n) (λ x₁ → πₙ (A , B) (x (suc n) x₁)) ≡ x n)
--             ((n : ℕ) → transport (λ x₁ → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x₂ → x₂)) (fst a , snd a)) → W (A , B) n)
--                                  (λ x₁ → πₙ (A , B) (fun (lemma11-temp (fst a , snd a)) x (suc n) x₁)) ≡ fun (lemma11-temp (fst a , snd a)) x n)
--       fun (lemma11-temp-2-ext (a , p) x) x₁ n = fun (lemma11-temp-2 (a , p) x n) (x₁ n)
--       inv (lemma11-temp-2-ext (a , p) x) x₁ n = inv (lemma11-temp-2 (a , p) x n) (x₁ n)
--       rightInv (lemma11-temp-2-ext (a , p) x) x₁ i n = rightInv (lemma11-temp-2 (a , p) x n) (x₁ n) i
--       leftInv (lemma11-temp-2-ext (a , p) x) x₁ i n = leftInv (lemma11-temp-2 (a , p) x n) (x₁ n) i



  -- (Σ (L ((λ _ → A) ,, λ x → x)) λ a →
  --    Σ ((n : ℕ) → B (a .fst n) → W S n) λ u →
  --      (n : ℕ) → transport (λ x → B (a .snd n x) → W S n) (πₙ S ∘ u (suc n)) ≡ (u n))
  --   Iso⟨ Σ-ap-iso (lemma11-Iso {S = S} (λ _ → A) λ _ x → x) (λ {(a , p) →
  --      Σ-ap-iso (lemma11-temp (a , p)) (lemma11-temp-2-ext (a , p))}) ⟩
  -- (Σ A λ a → Σ ((n : ℕ) → B a → W S n) λ u →
  --    (n : ℕ) → transport (λ x → B a → W S n) (πₙ S ∘ u (suc n)) ≡ (u n))
  --   Iso⟨ Σ-ap-iso₂ (λ a → Σ-ap-iso₂ λ u →
  --        iso (λ x n → subst (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n)))) (x n))
  --            (λ x n → subst (λ k → k n ≡ u n) (sym (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))) (x n))
  --            (λ b i n → transportTransport⁻ (cong (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))) (b n) i)
  --            (λ b i n → transport⁻Transport (cong (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))) (b n) i)) ⟩
  -- Σ A (λ a → Σ ((n : ℕ) → B a → W S n) λ u →
  --    (n : ℕ) → πₙ S ∘ u (suc n) ≡ u n) ∎Iso


α-iso-step-5'-Iso : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso
      (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
        Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
          (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
      (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
α-iso-step-5'-Iso {S = S@(A , B)} =
  (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) (λ a →
     Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
       (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n)))
    Iso⟨ Σ-ap-iso (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) (λ { (a , p) → Σ-ap-iso (lemma11-temp (a , p)) (lemma11-temp-2-ext (a , p)) }) ⟩
  Σ A (λ a → Σ ((n : ℕ) → B a → W S n) λ u → (n : ℕ) → transport (λ x → B a → W S n) (πₙ S ∘ u (suc n)) ≡ u n)
    Iso⟨ Σ-ap-iso₂ (λ a → Σ-ap-iso₂ λ u → pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → cong (λ k → k n ≡ u n) (funExt (λ n → transportRefl (πₙ S ∘ u (suc n))))))) ⟩
  Σ A (λ a → Σ ((n : ℕ) → B a → W S n) λ u → (n : ℕ) → πₙ S ∘ u (suc n) ≡ u n) ∎Iso
    where
      lemma11-temp-Path :
        (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n))
        → ((n : ℕ) → B (a .fst n) → W (A , B) n)
        ≡ ((n : ℕ) → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) a) → W (A , B) n)
      lemma11-temp-Path a = cong (λ k → (n : ℕ) → k n) (funExt λ n → λ i → B (lemma11-2-Iso {S = S} (a .fst) (a .snd) n i) → W (A , B) n)

      lemma11-temp :
        (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
          Iso
            ((n : ℕ) → B (a .fst n) → W (A , B) n)
            ((n : ℕ) → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) a) → W (A , B) n)
      lemma11-temp = pathToIso ∘ lemma11-temp-Path 

      kasd :
        forall m n a b ->
          (transport n (transport m a) ≡ (transport n b)) ≡ (transport m a ≡ b)
      kasd m n a b =
        transport n (transport m a) ≡ transport n b
          ≡⟨ (≡-rel-a-inj-x (pathToIso n)) ⟩
        transport m a ≡ b ∎  

      lemma11-temp-2 :
        (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
        (x : (n : ℕ) → B (a .fst n) → X (sequence (A , B)) n) →
        (n : ℕ) → 
        Iso
          (PathP (λ x₁ → B (a .snd n x₁) → W (A , B) n) (λ x₁ → πₙ (A , B) (x (suc n) x₁)) (x n))
          (transport (λ i → B (a .fst 0) → W (A , B) n) (λ x₁ → πₙ (A , B) (fun (lemma11-temp a) x (suc n) x₁)) ≡ fun (lemma11-temp a) x n)
      lemma11-temp-2 a x n =
        PathP (λ x₁ → B (a .snd n x₁) → W (A , B) n) (πₙ (A , B) ∘ (x (suc n))) (x n)
          Iso⟨ pathToIso (PathP≡Path (λ x₁ → B (a .snd n x₁) → W (A , B) n) (πₙ (A , B) ∘ (x (suc n))) (x n)) ⟩
        transport (λ x₁ → B (a .snd n x₁) → W (A , B) n) (πₙ (A , B) ∘ (x (suc n))) ≡ x n
          Iso⟨ {!!} ⟩
        transport (λ i → B (a .fst 0) → W (A , B) n) (πₙ (A , B) ∘ (fun (lemma11-temp a) x (suc n))) ≡ fun (lemma11-temp a) x n ∎Iso
      -- fun (lemma11-temp-2 a x n) = {!!}
      -- inv (lemma11-temp-2 a x n) = {!!}
      -- rightInv (lemma11-temp-2 a x n) = {!!}
      -- leftInv (lemma11-temp-2 a x n) = {!!}

      lemma11-temp-2-ext :
        (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
        (x : (n : ℕ) → B (a .fst n) → X (sequence (A , B)) n) →
        Iso
          ((n : ℕ) → PathP (λ x₁ → B (a .snd n x₁) → W (A , B) n) (λ x₁ → πₙ (A , B) (x (suc n) x₁)) (x n))
          ((n : ℕ) → transport (λ i → B (a .fst 0) → W (A , B) n) (λ x₁ → πₙ (A , B) (fun (lemma11-temp a) x (suc n) x₁)) ≡ fun (lemma11-temp a) x n)
      lemma11-temp-2-ext a x = pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → isoToPath (lemma11-temp-2 a x n)))

      -- lemma11-temp-2-ext :
      --     (a : Σ ((n : ℕ) → A) (λ x → (n : ℕ) → x (suc n) ≡ x n)) →
      --     (x : (n : ℕ) → B (a .fst n) → W (A , B) n) →
      --     Iso
      --       ((n : ℕ) → PathP (λ x₁ → B (snd a n x₁) → W (A , B) n) (λ x₁ → πₙ (A , B) (x (suc n) x₁)) ≡ x n)
      --       ((n : ℕ) → PathP (λ x₁ → B (fun (lemma11-Iso {S = S} (λ _ → A) (λ _ x₂ → x₂)) (fst a , snd a)) → W (A , B) n)
      --                            (λ x₁ → πₙ (A , B) (fun (lemma11-temp (fst a , snd a)) x (suc n) x₁)) ≡ fun (lemma11-temp (fst a , snd a)) x n)
      -- fun (lemma11-temp-2-ext (a , p) x) x₁ n = fun (lemma11-temp-2 (a , p) x n) (x₁ n)
      -- inv (lemma11-temp-2-ext (a , p) x) x₁ n = inv (lemma11-temp-2 (a , p) x n) (x₁ n)
      -- rightInv (lemma11-temp-2-ext (a , p) x) x₁ i n = rightInv (lemma11-temp-2 (a , p) x n) (x₁ n) i
      -- leftInv (lemma11-temp-2-ext (a , p) x) x₁ i n = leftInv (lemma11-temp-2 (a , p) x n) (x₁ n) i

sym-α-iso-step-5-Iso : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso
      (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
      (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
        Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
          (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))
sym-α-iso-step-5-Iso {S = S@(A , B)} = sym-iso α-iso-step-5'-Iso
  -- Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ u (suc n) ≡ u n)
  --   Iso⟨ sym-iso α-iso-step-5'-Iso ⟩
  -- (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) λ a →
  --    Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
  --      (n : ℕ) → transport (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) ≡ (u n))
  --   Iso⟨ Σ-ap-iso₂ (λ {(x , y) →
  --        Σ-ap-iso₂ λ {z → pathToIso (cong (λ a → (n : ℕ) → a n) (funExt λ n → sym (PathP≡Path (λ x → B (y n x) → X (sequence S) n) (πₙ S ∘ z (suc n)) (z n))))}}) ⟩
  -- (Σ (Σ ((n : ℕ) → A) (λ a → (n : ℕ) → a (suc n) ≡ a n)) (λ a →
  --    Σ ((n : ℕ) → B (a .fst n) → X (sequence S) n) λ u →
  --      (n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n) (π (sequence S) ∘ u (suc n)) (u n))) ∎Iso

sym-α-iso-step-6 : ∀ {ℓ} {S : Container {ℓ}}
    -> let (A , B) = S in
    Iso (Σ A (λ a → B a → M S))
        (Σ A (λ a → Σ ((n : ℕ) → B a → X (sequence S) n) λ u → (n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n))
sym-α-iso-step-6 {S = S@(A , B)} = Σ-ap-iso₂ λ x → lemma10-Iso {C,γ = B x , λ _ → x , (λ x₁ → x₁)}

-- Lemma 13
α-iso : ∀ {ℓ} {S : Container {ℓ}} -> L (PX,Pπ S) ≡ P₀ {S = S} (M S) -- L^P ≡ PL
α-iso {S = S@(A , B)} = isoToPath (compIso (α-iso-step-1-4-Iso) (compIso (sym-iso sym-α-iso-step-5-Iso) (sym-iso sym-α-iso-step-6)))

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
shift-iso {S = S@(A , B)} = (compIso sym-α-iso-step-6 (compIso (sym-α-iso-step-5-Iso {S = S}) (comp-α-iso-step-1-4-Iso-Sym-L-unique-iso {S = S})))

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
