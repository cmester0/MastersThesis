{-# OPTIONS --cubical --safe --guardedness --copatterns #-}

module stream where

  open import Cubical.Foundations.Everything
  open import Cubical.Core.Everything

  open import Cubical.Data.Nat as ℕ using (ℕ ; suc)
  open import Cubical.Data.Empty
  open import Cubical.Data.Unit
  open import Cubical.Data.Prod
  open import Cubical.Data.Sum
  open import Cubical.Data.Bool

  open import Cubical.Codata.M

  -- Type
  stream : Set -> Set
  stream A = M ((λ { tt → A } ) , (λ {tt _ tt → Unit } )) tt -- stream A = M (Stream, tail)

  -- Definitions
  stream-hd : ∀ {A} -> stream A -> A
  stream-hd s = s .head -- out tt s .fst

  stream-tl : ∀ {A} -> stream A -> stream A
  stream-tl s = s .tails tt tt -- out tt s .snd tt tt

  -- General definition
  stream-n-tl : ∀ {A} -> ℕ -> stream A -> stream A
  stream-n-tl 0 s = s
  stream-n-tl (suc n) s = stream-tl (stream-n-tl n s)

  stream-nth : ∀ {A} -> ℕ -> stream A -> A
  stream-nth n s = stream-hd (stream-n-tl n s)

  -- Bisimulation
  record _≈_ {A : Type₀} (x y : stream A) : Type₀ where
    coinductive
    field
      ≈head : stream-hd x ≡ stream-hd y
      ≈tail : stream-tl x ≈ stream-tl y

  open _≈_

  bisim : {A : Type₀} → {x y : stream A} → x ≈ y → x ≡ y
  head (bisim x≈y i)        = ≈head x≈y i
  tails (bisim x≈y i) tt tt = bisim (≈tail x≈y) i

  misib : {A : Type₀} → {x y : stream A} → x ≡ y → x ≈ y
  ≈head (misib p) =        λ i → stream-hd (p i)
  ≈tail (misib p) = misib (λ i → stream-tl (p i))

  iso1 : {A : Type₀} → {x y : stream A} → (p : x ≡ y) → bisim (misib p) ≡ p
  head  (iso1 p i j)       = stream-hd (p j)
  tails (iso1 p i j) tt tt = iso1 (λ i → stream-tl (p i)) i j

  iso2 : {A : Type₀} → {x y : stream A} → (p : x ≈ y) → misib (bisim p) ≡ p
  ≈head (iso2 p i) = ≈head p
  ≈tail (iso2 p i) = iso2 (≈tail p) i

  path≃bisim : {A : Type₀} → {x y : stream A} → (x ≡ y) ≃ (x ≈ y)
  path≃bisim = isoToEquiv (iso misib bisim iso2 iso1)

  path≡bisim : {A : Type₀} → {x y : stream A} → (x ≡ y) ≡ (x ≈ y)
  path≡bisim = ua path≃bisim

  -- Examples
  zero-stream : stream ℕ
  head zero-stream        = 0
  tails zero-stream tt tt = zero-stream

  const-stream : ∀ n -> stream ℕ
  head  (const-stream n)       = n
  tails (const-stream n) tt tt = const-stream n

  mapS : ∀ {A B} -> (A -> B) -> stream A -> stream B
  head  (mapS f s)       = f (stream-hd s)
  tails (mapS f s) tt tt = mapS f (stream-tl s)

  const'-stream : ∀ (n : ℕ) -> stream ℕ
  const'-stream n = mapS (λ _ -> n) zero-stream

  const-eq : ∀ n -> const-stream n ≈ const'-stream n
  ≈head (const-eq n) = refl
  ≈tail (const-eq n) = const-eq n

  const-eq-2 : ∀ n -> const-stream n ≈ const'-stream n
  ≈head (const-eq-2 n) = refl
  ≈tail (const-eq-2 n) = record { ≈head = refl ; ≈tail = const-eq n }

  mapS-id : ∀ {A} {xs : stream A} → mapS (λ x → x) xs ≡ xs
  head (mapS-id {xs = xs} i) = stream-hd xs
  tails (mapS-id {xs = xs} i) = λ { tt tt -> mapS-id {xs = stream-tl xs} i }

  nat-stream' : ∀ (n : ℕ) -> stream ℕ
  nat-stream' n .head = n
  nat-stream' n .tails = λ { _ tt -> nat-stream' (suc n) }

  nat-stream = nat-stream' 0

  nat-stream-equality-test : stream-nth 100 nat-stream ≡ 100
  nat-stream-equality-test = refl
