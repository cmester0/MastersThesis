{-# OPTIONS --cubical --guardedness #-} --safe

open import M.Base
open import M.Properties

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Codata.Stream

open import helper
open import Container

module stream where

--------------------------------------
-- Stream definitions using M-types --
--------------------------------------

stream-S : ∀ A -> Container
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Set₀) -> Set₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

-- --------------------------
-- -- Stream using M-types --
-- --------------------------

stream-pair-M : ∀ A B → stream A × stream B ≡ M (Container-product (stream-S A) (stream-S B))
stream-pair-M A B = M-product-equality (stream-S A) (stream-S B)

Container-product-streams : ∀ A B → Container-product (stream-S A) (stream-S B) ≡ stream-S (A × B)
Container-product-streams A B =
  Container-product (stream-S A) (stream-S B)
    ≡⟨ refl ⟩
  (A × B , λ x → Unit × Unit )
    ≡⟨ (λ i → (A × B) , λ _ → sym diagonal-unit i) ⟩
  (A × B , λ x → Unit ) 
    ≡⟨ refl ⟩
  stream-S (A × B) ∎

stream-pair : ∀ A B → stream A × stream B ≡ stream (A × B)
stream-pair A B = stream-pair-M A B □ λ i → M (Container-product-streams A B i)

zip : ∀ {A B} → stream A × stream B → stream (A × B)
zip {A} {B} = transport (stream-pair A B)

--------------------------
-- Stream using M-types --
--------------------------

stream-zip-x : ∀ {A B} (n : ℕ) -> stream A × stream B → X (sequence (Container-product (stream-S A) (stream-S B))) n
stream-zip-x 0 x = lift tt
stream-zip-x (suc n) (x , y) = (hd x , hd y) , λ _ → stream-zip-x n ((tl x) , (tl y))

stream-zip-π : ∀ {A B} (n : ℕ) (a : stream A × stream B) → π (sequence (Container-product (stream-S A) (stream-S B))) (stream-zip-x (suc n) a) ≡ stream-zip-x n a
stream-zip-π 0 a = refl
stream-zip-π (suc n) (x , y) = λ i → (hd x , hd y) , λ _ → stream-zip-π n (tl x , tl y) i

lift-zip : ∀ {A B} → stream A × stream B → stream (A × B)
lift-zip {A} {B} x = transport (λ i -> M (Container-product-streams A B i)) (lifting stream-zip-x stream-zip-π x)

postulate
  transport-compose : ∀ {ℓ} {A B C : Set ℓ} (a : A ≡ B) (b : B ≡ C) (c : A) -> transport (a □ b) c ≡ transport b (transport a c)

transport-iso : ∀ {ℓ} {X Y : Set ℓ} {A : X → Y} {B C D} {x : X} → transport (isoToPath (iso A B C D)) x ≡ A x
transport-iso {A = A} {x = x} = transportRefl (A x)

transport-cong : ∀ (A B C : Set) (k : A) (y : B) (P : B ≡ C) → transport (cong (λ a → Σ A λ x → a) P) (k , y) ≡ (k , transport P y)
transport-cong A B C k y P =
  transport (cong (λ a → Σ A λ x → a) P) (k , y)
    ≡⟨ refl ⟩
  transport (λ i → Σ A λ x → P i) (k , y)
    ≡⟨ {!!} ⟩
  (k , transport P y) ∎

postulate
  zip-equality-helper-2 :
    ∀ {A B} (x : stream A × stream B) →
    ∀ n →
    ((hd (proj₁ x) , hd (proj₂ x)) , (λ a → stream-zip-x n (tl (proj₁ x) , tl (proj₂ x)))) ≡
    (((proj₁ x) .fst (suc n) .fst , (proj₂ x) .fst (suc n) .fst) , transport (λ i → Unit × Unit → P-equality n i)
      (λ y → ((proj₁ x) .fst (suc n) .snd (proj₁ x) , (proj₂ x) .fst (suc n) .snd (proj₂ x))))

zip-equality-helper : ∀ {A B} (x : stream A × stream B) → (lifting stream-zip-x stream-zip-π x) ≡ (transport (M-product-equality (stream-S A) (stream-S B)) x)
zip-equality-helper {A} {B} (a , b) =
  lifting stream-zip-x stream-zip-π (a , b)
    ≡⟨ refl ⟩
  (λ n → stream-zip-x n (a , b)) ,
  (λ n → stream-zip-π n (a , b))
    ≡⟨ transport Σ-split-iso (funExt (λ {0 → refl ; (suc n) → refl}) , λ {i 0 → refl ; i (suc n) → stream-zip-π (suc n) (a , b)}) ⟩
  (λ {0 → lift tt ; (suc n) → (hd a , hd b) , λ _ → stream-zip-x n ((tl a) , (tl b))}) ,
  (λ {0 → refl ; (suc n) → λ i → (hd a , hd b) , λ _ → stream-zip-π n (tl a , tl b) i})
    ≡⟨ transport Σ-split-iso (funExt (λ {0 → refl ; (suc n) →
       (((hd a , hd b) , λ x → stream-zip-x n (tl a , tl b))
         ≡⟨ zip-equality-helper-2 (a , b) n ⟩
       ((a .fst (suc n) .fst , b .fst (suc n) .fst) , transport (λ i → Unit × Unit → P-equality n i) (λ x → (a .fst (suc n) .snd (proj₁ x) , b .fst (suc n) .snd (proj₂ x))))
         ≡⟨ sym (transport-cong (A × B) (Unit × Unit → P-equality n i0) (Unit × Unit → P-equality n i1) (a .fst (suc n) .fst , b .fst (suc n) .fst) (λ x → a .fst (suc n) .snd (proj₁ x) , b .fst (suc n) .snd (proj₂ x)) λ i → Unit × Unit → P-equality n i ) ⟩
       transport (cong (λ y → Σ (A × B) λ x → y) (λ i → Unit × Unit → P-equality n i))
         ((a .fst (suc n) .fst , b .fst (suc n) .fst) , (λ x → a .fst (suc n) .snd (proj₁ x) , b .fst (suc n) .snd (proj₂ x)))
         ≡⟨ refl ⟩
       transport (cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n))
         ((a .fst (suc n) .fst , b .fst (suc n) .fst) , (λ x → a .fst (suc n) .snd (proj₁ x) , b .fst (suc n) .snd (proj₂ x)))
         ≡⟨ cong (λ a₁ → transport (cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n)) ((a .fst (suc n) .fst , b .fst (suc n) .fst) , a₁)) (λ {i (tt , tt) → a .fst (suc n) .snd tt , b .fst (suc n) .snd tt}) ⟩
       transport (cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n))
         ((a .fst (suc n) .fst , b .fst (suc n) .fst) , (Σ-prod-fun₁ n (a .fst (suc n) .fst , b .fst (suc n) .fst)) (a .fst (suc n) .snd , b .fst (suc n) .snd))
         ≡⟨ cong (λ a₁ → transport (cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n)) ((a .fst (suc n) .fst , b .fst (suc n) .fst) , a₁)) (sym (transportRefl (Σ-prod-fun₁ n (a .fst (suc n) .fst , b .fst (suc n) .fst) (a .fst (suc n) .snd , b .fst (suc n) .snd)))) ⟩
       transport (cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n))
         ((a .fst (suc n) .fst , b .fst (suc n) .fst) ,
         transport (isoToPath (iso (Σ-prod-fun₁ n (a .fst (suc n) .fst , b .fst (suc n) .fst))
                                   (Σ-prod-fun₂ n (a .fst (suc n) .fst , b .fst (suc n) .fst))
                                   (Σ-prod-iso₁ n (a .fst (suc n) .fst , b .fst (suc n) .fst))
                                   (Σ-prod-iso₂ n (a .fst (suc n) .fst , b .fst (suc n) .fst))))
                   (a .fst (suc n) .snd , b .fst (suc n) .snd))
         ≡⟨ refl ⟩
       transport (cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n))
         ((a .fst (suc n) .fst , b .fst (suc n) .fst) ,
         transport (Σ-prod-fun n (a .fst (suc n) .fst , b .fst (suc n) .fst)) (a .fst (suc n) .snd , b .fst (suc n) .snd))
         ≡⟨ cong (transport (cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n))) (sym (transportRefl ((a .fst (suc n) .fst , b .fst (suc n) .fst) , transport (Σ-prod-fun n (a .fst (suc n) .fst , b .fst (suc n) .fst)) (a .fst (suc n) .snd , b .fst (suc n) .snd)))) ⟩
       transport (cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n))
         (transport (Σ-ap-iso₂ (Σ-prod-fun n)) ((a .fst (suc n) .fst , b .fst (suc n) .fst) , ( a .fst (suc n) .snd , b .fst (suc n) .snd)))
         ≡⟨ sym (transport-compose (Σ-ap-iso₂ (Σ-prod-fun n)) (cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n)) ((a .fst (suc n) .fst , b .fst (suc n) .fst) , (a .fst (suc n) .snd , b .fst (suc n) .snd))) ⟩
       transport (Σ-ap-iso₂ (Σ-prod-fun n) □ cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n)) ((a .fst (suc n) .fst , b .fst (suc n) .fst) , ( a .fst (suc n) .snd , b .fst (suc n) .snd))
         ≡⟨ cong (transport (Σ-ap-iso₂ (Σ-prod-fun n) □ cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n))) (sym (transportRefl ((a .fst (suc n) .fst , b .fst (suc n) .fst) , (a .fst (suc n) .snd , b .fst (suc n) .snd)))) ⟩
       transport (Σ-ap-iso₂ (Σ-prod-fun n) □ cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n))
                 (transport {A = Σ A (λ a → Unit → W (A , λ _ → Unit) n) × Σ B (λ c → Unit → W (B , λ _ → Unit) n)}
                            {B = Σ (A × B) (λ x → (Unit → W (A , λ _ → Unit) n) × (Unit → W (B , λ _ → Unit) n))}
                              (isoToPath (iso (λ x → ((proj₁ x) .fst , (proj₂ x) .fst) , ((proj₁ x) .snd , (proj₂ x) .snd))
                                              (λ x → (proj₁ (x .fst) , proj₁ (x .snd)) , ((proj₂ (x .fst)) , (proj₂ (x .snd))))
                                              (λ { ((a , c) , b , d) → refl })
                                              (λ { ((a , c) , b , d) → refl }))) (a .fst (suc n) , b .fst (suc n)))
         ≡⟨ refl ⟩
       transport (Σ-ap-iso₂ (Σ-prod-fun n) □ cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n)) (transport (P-equality-helper n) (a .fst (suc n) , b .fst (suc n)))
         ≡⟨ sym (transport-compose {A = Σ A (λ a₁ → Unit → W (A , (λ _ → Unit)) n) × Σ B (λ c → Unit → W (B , (λ _ → Unit)) n)} {B = Σ (A × B) (λ x → (Unit → W (A , (λ x₁ → Unit)) n) × (Unit → W (B , (λ x₁ → Unit)) n))} {C = Σ (A × B) (λ x → Unit × Unit → W (Container-product (A , (λ v → Unit)) (B , (λ v → Unit))) n)} (P-equality-helper {A = A} {C = B} {B = λ x → Unit} {D = λ x → Unit} n) (Σ-ap-iso₂ (Σ-prod-fun n) □ cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n)) (a .fst (suc n) , b .fst (suc n))) ⟩ 
       transport (P-equality-helper n □ (Σ-ap-iso₂ (Σ-prod-fun n) □ cong (λ y → Σ (A × B) λ x → Unit × Unit → y) (P-equality n))) (a .fst (suc n) , b .fst (suc n))
         ≡⟨ refl ⟩
       transport (P-equality (suc n)) (a .fst (suc n) , b .fst (suc n)) ∎)
      }) , λ {i 0 → refl ; i (suc n) → {!!}}) ⟩
  (λ n → transport (P-equality {A = A} {C = B} {B = λ _ → Unit} {D = λ _ → Unit} n) (a .fst n , b .fst n)) ,
  π-equality {B = λ _ → Unit} {D = λ _ → Unit} (λ n -> transport (P-equality n) (a .fst n , b .fst n))
    ≡⟨ refl ⟩
  (λ n → transport (P-equality n) (a .fst n , b .fst n)) ,
  π-equality {B = λ _ → Unit} {D = λ _ → Unit} (λ n -> transport (P-equality n) (a .fst n , b .fst n))
    ≡⟨ refl ⟩
  (M-product (stream-S A) (stream-S B)) (a , b)
    ≡⟨ sym (transport-iso
           {A = M-product (stream-S A) (stream-S B)}
           {B = M-product-inv (stream-S A) (stream-S B)}
           {C = M-product-iso₁ (stream-S A) (stream-S B)}
           {D = M-product-iso₂ (stream-S A) (stream-S B)} {x = (a , b)}) ⟩
  transport
    (isoToPath
     (iso (M-product (stream-S A) (stream-S B))
          (M-product-inv (stream-S A) (stream-S B))
          (M-product-iso₁ (stream-S A) (stream-S B))
          (M-product-iso₂ (stream-S A) (stream-S B))))
    (a , b)
    ≡⟨ refl ⟩
  transport (M-product-equality (stream-S A) (stream-S B)) (a , b) ∎

-- transport (isoToPath (iso (M-product (stream-S A) (stream-S B)) (M-product-inv (stream-S A) (stream-S B)) (M-product-iso₁ (stream-S A) (stream-S B)) (M-product-iso₂ (stream-S A) (stream-S B))))

-- Todo show equality of zip functions !
zip-equality : ∀ {A B} → lift-zip {A = A} {B = B} ≡ zip
zip-equality {A} {B} i (a , b) =
  (lift-zip (a , b)
    ≡⟨ refl ⟩
  transport (λ i → M (Container-product-streams A B i)) (lifting stream-zip-x stream-zip-π (a , b))
    ≡⟨ (λ j → transport (λ i → M (Container-product-streams A B i)) (zip-equality-helper (a , b) j)) ⟩
  transport (λ i → M (Container-product-streams A B i)) (transport (M-product-equality (stream-S A) (stream-S B)) (a , b))
    ≡⟨ sym (transport-compose (M-product-equality (stream-S A) (stream-S B)) (λ i → M (Container-product-streams A B i)) (a , b)) ⟩
  transport (M-product-equality (stream-S A) (stream-S B) □ λ i → M (Container-product-streams A B i)) (a , b)
    ≡⟨ refl ⟩
  transport (stream-pair-M A B □ λ i → M (Container-product-streams A B i)) (a , b)
    ≡⟨ refl ⟩
  transport (stream-pair A B) (a , b)
    ≡⟨ refl ⟩
  zip (a , b) ∎) i

-- ------------------------------
-- -- Equality of stream types --
-- ------------------------------

-- open Stream

-- stream-to-Stream : ∀ {A} → stream A → Stream A
-- head (stream-to-Stream x) = (hd x)
-- tail (stream-to-Stream x) = (stream-to-Stream (tl x))

-- Stream-to-stream-func-x : ∀ {A} (n : ℕ) -> Stream A → X (sequence (stream-S A)) n
-- Stream-to-stream-func-x 0 x = lift tt
-- Stream-to-stream-func-x (suc n) x = head x , λ x₁ → Stream-to-stream-func-x n (tail x)

-- Stream-to-stream-func-π : ∀ {A} (n : ℕ) (a : Stream A) → π (sequence (stream-S A)) (Stream-to-stream-func-x (suc n) a) ≡ Stream-to-stream-func-x n a
-- Stream-to-stream-func-π 0 a = refl
-- Stream-to-stream-func-π (suc n) a = λ i → head a , λ _ → Stream-to-stream-func-π n (tail a) i

-- Stream-to-stream : ∀ {A : Set} -> Stream A -> stream A
-- Stream-to-stream s = lifting Stream-to-stream-func-x Stream-to-stream-func-π s

-- -- Stream-to-stream (stream-to-stream a)
-- -- Stream-to-stream (record { head = hd a ; tail = stream-to-stream (tl a) })
-- -- lifting Stream-to-stream-func-x Stream-to-stream-func-π (record { head = hd a ; tail = stream-to-Stream (tl a) })
-- -- (λ x p a → (λ n → x n a) , λ n i → p n a i) Stream-to-stream-func-x Stream-to-stream-func-π (record { head = hd a ; tail = stream-to-Stream (tl a) })
-- -- (λ a → (λ n → Stream-to-stream-func-x n a) , λ n i → Stream-to-stream-func-π n a i) (record { head = hd a ; tail = stream-to-Stream (tl a) })
--   -- First case:
--   -- (λ n → Stream-to-stream-func-x n (record { head = hd a ; tail = stream-to-Stream (tl a) }))
--     -- Zero case
--     -- Stream-to-stream-func-x 0 (record { head = hd a ; tail = stream-to-Stream (tl a) })
--     -- lift tt
--     -- N+1 case:
--     -- Stream-to-stream-func-x (suc n) (record { head = hd a ; tail = stream-to-Stream (tl a) })
--     -- (hd a , λ x₁ → Stream-to-stream-func-x n (stream-to-Stream (tl a)))
--   -- Second case:
--   -- λ n i → Stream-to-stream-func-π n (record { head = hd a ; tail = stream-to-Stream (tl a) }) i) 

-- stream-equality-iso-1-helper-0 : ∀ {A} (b : Stream A) -> (hd (Stream-to-stream b)) ≡ (head b)
-- stream-equality-iso-1-helper-0 {A} b = 
--   hd (Stream-to-stream b)
--     ≡⟨ refl ⟩
--   hd (lifting Stream-to-stream-func-x Stream-to-stream-func-π b)
--     ≡⟨ refl ⟩
--   hd ((λ n → Stream-to-stream-func-x n b) , λ n i → Stream-to-stream-func-π n b i)
--     ≡⟨ refl ⟩
--   out-fun ((λ n → Stream-to-stream-func-x n b) , (λ n i → Stream-to-stream-func-π n b i)) .fst
--     ≡⟨ refl ⟩
--   transport (sym (shift {S = stream-S A})) (((λ n → Stream-to-stream-func-x n b) , (λ n i → Stream-to-stream-func-π n b i))) .fst
--     ≡⟨ refl ⟩
--   transport (sym ((sym α-iso') □ (L-unique' {S = stream-S A}))) (((λ n → Stream-to-stream-func-x n b) , (λ n i → Stream-to-stream-func-π n b i))) .fst
--     ≡⟨ refl ⟩
--   transport (sym ((sym α-iso') □ (L-unique' {S = stream-S A}))) (((λ n → Stream-to-stream-func-x n b) , (λ n i → Stream-to-stream-func-π n b i))) .fst
--     ≡⟨ {!!} ⟩
--   head b ∎

-- stream-equality-iso-1 : ∀ {A} → (b : Stream A) → stream-to-Stream (Stream-to-stream b) ≡ b
-- stream-equality-iso-1 b =
--   stream-to-Stream (Stream-to-stream b)
--     ≡⟨ {!!} ⟩
--   stream-to-Stream (cons (hd (Stream-to-stream b)) (tl (Stream-to-stream b)))
--     ≡⟨ (λ i → stream-to-Stream (cons {!!} (tl (Stream-to-stream b)))) ⟩
--   stream-to-Stream (cons (head b) (tl (Stream-to-stream b)))
--     ≡⟨ {!!} ⟩
--   b ∎
  
-- -- stream-equality-iso-1 : ∀ {A} → (b : Stream A) → stream-to-Stream (Stream-to-stream b) ≡ b
-- -- head (stream-equality-iso-1 b i) =
-- --   (head (stream-to-Stream (Stream-to-stream b))
-- --     ≡⟨ refl ⟩
-- --   hd (Stream-to-stream b)
-- --     ≡⟨ {!!} ⟩
-- --   head b ∎) i
-- -- tail (stream-equality-iso-1 b i) =
-- --   (tail (stream-to-Stream (Stream-to-stream b))
-- --     ≡⟨ refl ⟩
-- --   (stream-to-Stream (tl (Stream-to-stream b)))
-- --     ≡⟨ {!!} ⟩
-- --   stream-to-Stream (Stream-to-stream (tail b))
-- --     ≡⟨ stream-equality-iso-1 (tail b) ⟩
-- --   tail b ∎) i

-- -- stream-to-Stream : ∀ {A} → stream A → Stream A
-- -- head (stream-to-Stream x) = (hd x)
-- -- tail (stream-to-Stream x) = (stream-to-Stream (tl x))

-- -- stream-equality-iso-2₁ : ∀ {A} → (a : stream A) → (λ n → Stream-to-stream-func-x n (record { head = hd a ; tail = stream-to-Stream (tl a) })) ≡ a .fst
-- -- stream-equality-iso-2₁  a i 0 = lift tt
-- -- stream-equality-iso-2₁  a i (suc n) = {!!} , λ x → {!!}

-- -- stream-equality-iso-2 : ∀ {A} → (a : stream A) → Stream-to-stream (stream-to-Stream a) ≡ a
-- -- stream-equality-iso-2 a =
-- --   Stream-to-stream (stream-to-Stream a)
-- --     ≡⟨ refl ⟩
-- --   (λ n → Stream-to-stream-func-x n (stream-to-Stream a)) ,
-- --   (λ n i → Stream-to-stream-func-π n (stream-to-Stream a) i)
-- --     ≡⟨ {!!} ⟩
-- --   (λ n → Stream-to-stream-func-x n (record { head = hd a ; tail = stream-to-Stream (tl a) })) ,
-- --   (λ n i → Stream-to-stream-func-π n (record { head = hd a ; tail = stream-to-Stream (tl a) }) i)
-- --     ≡⟨ (λ i → stream-equality-iso-2₁ a i , {!!}) ⟩
-- --   (a .fst , a .snd)
-- --     ≡⟨ refl ⟩
-- --   a ∎

-- -- stream-equality : ∀ {A} -> stream A ≡ Stream A
-- -- stream-equality = isoToPath (iso stream-to-Stream Stream-to-stream stream-equality-iso-1 stream-equality-iso-2)

-- -- -- Defining stream examples by transporting records

-- -- Zeros : Stream ℕ
-- -- head Zeros = 0
-- -- tail Zeros = Zeros

-- -- zeros : stream ℕ
-- -- zeros = transport (sym stream-equality) Zeros

