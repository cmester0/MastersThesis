{-# OPTIONS --cubical --safe #-} 
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

isProp1 : ∀ {ℓ} (X : Set ℓ) → Set ℓ
isProp1 X = (x y : X) → x ≡ y

isProp2 : ∀ {ℓ} (X : Set ℓ) → Set ℓ
isProp2 X = (x y : X) → isContr (x ≡ y)

ex1 : ∀ {ℓ} (X : Set ℓ) → isProp1 X ≡ isProp2 X
ex1 X = isoToPath (iso
    (λ p x y →
      let temp = contrSingl (p x y) in
      (p x y) , J (λ y q → p x y ≡ q) {!!}
      -- (p x y j ≡⟨ p (p x y j) (q j) ⟩ q j ∎) {!!}
      -- let temp : p x y j ≡ q j
      --     temp = p (p x y j) (q j)
      -- in
      -- let temp' : temp i ≡ x
      --     temp' = {!!}
      -- in
      -- hcomp (λ k → λ {(j = i0) → p (p x y i0) (q i0) {!!} ; (j = i1) → {!!}}) (temp i) -- 
      -- temp i
      ) 
    (λ p x y → p x y .fst)
    {!!} {!!})
    -- (λ b → refl)
    -- λ a → refl)
-- λ q i j →  -- p x y ≡ q
--         let temp'' : x ≡ y
--             temp'' = (p x y) in
--         let temp' : y ≡ (q i)
--             temp' = p y (q i) in
--         let temp'3 : PathP (λ k → p x y k ≡ temp' k) temp'' temp'
--             temp'3 = {!!}
--         in
--         let temp'2 : temp'' j ≡ temp' j -- (x ≡ y) ≡ (y ≡ (q i))
--             temp'2 k = {!!} in -- p (p x y k) (p y (q i) k) {!!}
--         let temp'1 : p x y i ≡ q j
--             temp'1 = p (p x y i) (q j) in
--         {!!} -- temp'2 j
