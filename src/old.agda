
-- record coequalizer {ℓ} {X Y : Set ℓ} (f g : X -> Y) : Set (ℓ-suc ℓ) where
--   field
--     eqi : Σ (Set ℓ) (λ Q -> Σ (Y → Q) λ q -> q ∘ f ≡ q ∘ g)
--     uni : (eqi' : Σ (Set ℓ) (λ Q' -> Σ (Y → Q') λ q' -> q' ∘ f ≡ q' ∘ g)) -> Σ (eqi .fst -> eqi' .fst) (λ u -> u ∘ (eqi .snd .fst) ≡ (eqi' .snd .fst))

-- quotient : ∀ {ℓ} -> (S : Container {ℓ}) -> {x : Σ {!!} (λ F -> qpf {S = S} F {!!})} -> Set ℓ
-- quotient S {x = x} = QM (x .snd)

-- delay-tau' : {R : Set₀} -> delay R -> P₀ {S = delay-S R} (delay R)
-- delay-tau' S = (inl tt , λ x → S)

-- delay-tau : {R : Set₀} -> delay R -> delay R
-- delay-tau {R = R} x = M.in-fun (delay-tau' {R = R} x)

-- delay-ret : {R : Set₀} -> R -> delay R
-- delay-ret r = M.in-fun (inr r , λ ())

-- -- P⁻ : ∀ {ℓ} {S : Container {ℓ}} -> Functor {ℓ}

-- P⁻₀ : ∀ {S} -> Set -> Set
-- P⁻₀ {S = S} X  = Σ (A S) λ x → X -> (B S x)

-- P⁻₁ : ∀ {S} {X Y} -> (f : Y -> X) -> P⁻₀ {S = S} X -> P⁻₀ {S = S} Y
-- P⁻₁ f (a , g) = a , g ∘ f

-- repeat : ∀ {ℓ} {A : Set ℓ} -> (A → A) → ℕ → (A -> A)
-- repeat f 0 = λ x -> x
-- repeat f (suc n) = f ∘ (repeat f n)

-- terminating : ∀ {R} -> delay R -> R -> Set
-- terminating x r = Σ ℕ (λ n -> x ≡ repeat delay-tau n (delay-ret r))

-- delay-weak-bisim : ∀ {R} -> ∀ (x y : delay R) -> Set
-- delay-weak-bisim {R} x y = ∀ (a : R) → (terminating x a -> terminating y a) × (terminating y a -> terminating x a)

-- as : ∀ {R} x n r -> delay-weak-bisim {R = R} (repeat delay-tau n (delay-ret r)) (repeat delay-tau (suc n) (delay-ret r))
-- as = λ x n r -> λ a → (λ x₁ → {!!} , {!!}) , λ x₁ → {!!}



-- -- asdfasdf : ∀ {R} -> qpf {S = Ms (delay-S R)} (P {S = Ms (delay-S R)})
-- -- asdfasdf = record { abs = λ x → x ; repr = λ x → x ; abs_repr = λ x i a → a ; abs_map = λ f i a → a .fst , λ x → f (a .snd x) }
