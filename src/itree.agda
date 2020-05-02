{-# OPTIONS --cubical --guardedness #-} --safe

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv

open import Container
open import M
open import Coalg
open import helper

open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Functions.Embedding

module itree where

delay-helper : ∀ (R : Set) → (R ⊎ Unit) → Set
delay-helper R (inl _) = ⊥
delay-helper R (inr tt) = Unit

-- itrees (and buildup examples)
delay-S : (R : Set₀) -> Container
delay-S R = (R ⊎ Unit ) , delay-helper R

delay : (R : Set₀) -> Set₀
delay R = M (delay-S R)

-- ret = now
delay-ret : {R : Set} -> R -> delay R
delay-ret r = in-fun (inl r , λ ())

-- tau = later
delay-tau : {R : Set₀} -> delay R -> delay R
delay-tau t = in-fun (inr tt , λ _ → t)

mutual
  data Delay (R : Set) : Set where
    now : R → Delay R
    later : ∞Delay R → Delay R

  record ∞Delay (R : Set) : Set where
    coinductive
    field
      force : Delay R

-- open ∞Delay

-- mutual
--   ∞delay-to-Delay : ∀ {R} → P₀ {S = delay-S R} (delay R) → Delay R
--   ∞delay-to-Delay (inr r , b) = now r
--   ∞delay-to-Delay (inl tt , t) = later (delay-to-∞Delay (t tt))

--   delay-to-∞Delay : ∀ {R} → (delay R) → ∞Delay R
--   force (delay-to-∞Delay b) = delay-to-Delay b

--   delay-to-Delay : ∀ {R} → delay R → Delay R
--   delay-to-Delay {R} = M-coinduction-const (Delay R) ∞delay-to-Delay

-- Delay-to-delay-later-x : ∀ {R} → Delay R → (n : ℕ) → W (delay-S R) n
-- Delay-to-delay-later-x _ 0 = lift tt
-- Delay-to-delay-later-x (now r) (suc n) = inr r , λ _ → Delay-to-delay-later-x (now r) n
-- Delay-to-delay-later-x (later t) (suc n) = inl tt , λ _ → Delay-to-delay-later-x (force t) n

-- Delay-to-delay-later-π : ∀ {R} → (t : Delay R) → (n : ℕ) → πₙ (delay-S R) (Delay-to-delay-later-x t (suc n)) ≡ Delay-to-delay-later-x t n
-- Delay-to-delay-later-π _ 0 = refl {x = lift tt}
-- Delay-to-delay-later-π (now r) (suc n) i = inr r , λ _ → Delay-to-delay-later-π (now r) n i
-- Delay-to-delay-later-π (later t) (suc n) i = inl tt , λ _ → Delay-to-delay-later-π (force t) n i
  
-- Delay-to-delay : ∀ {R} → Delay R → delay R
-- Delay-to-delay (now r) = delay-ret r
-- Delay-to-delay (later t) = (Delay-to-delay-later-x (later t)) , Delay-to-delay-later-π (later t)

-- Delay-to-∞delay : ∀ {R} → Delay R → P₀ {S = delay-S R} (delay R)
-- Delay-to-∞delay (now r) = inr r , λ ()
-- Delay-to-∞delay (later t) = inl tt , λ { tt → Delay-to-delay (force t) }

-- ∞Delay-to-∞delay : ∀ {R} → ∞Delay R → P₀ {S = delay-S R} (delay R)
-- ∞Delay-to-∞delay f = Delay-to-∞delay (force f)

-- delay-equality-section : ∀ {R} (b : Delay R) → delay-to-Delay (Delay-to-delay b) ≡ b
-- delay-equality-section {R} (now r) = refl
-- delay-equality-section {R} (later t) = temp
--   where
--     postulate
--       temp : delay-to-Delay (Delay-to-delay (later t)) ≡ later t

-- --postulate
-- delay-equality-retraction : ∀ {R} (b : delay R) → Delay-to-delay (delay-to-Delay b) ≡ b
-- delay-equality-retraction {R} = M-coinduction (λ b' → Delay-to-delay (delay-to-Delay b') ≡ b')
--   (λ {(inr r , m) →
--     in-fun (inr r , λ ())
--       ≡⟨ cong (λ a → in-fun (inr r , a)) (isContr→isProp isContr⊥→A (λ ()) m) ⟩
--     in-fun (inr r , m) ∎
--   ; (inl tt , t) → temp t})
--   where
--     postulate
--       temp : ∀ t → Delay-to-delay (delay-to-Delay (in-fun (inl tt , t))) ≡ in-fun (inl tt , t)
--       -- temp' : ∀ t → Delay-to-delay (later (delay-to-∞Delay (t tt))) ≡ in-fun (inl tt , t)

  --   Delay-to-delay (delay-to-Delay (in-fun (inl tt , t)))
  --     ≡⟨ refl ⟩
  --   Delay-to-delay (M-coinduction-const (Delay R) ∞delay-to-Delay (in-fun (inl tt , t)))
  --     ≡⟨ {!!} ⟩
  --   Delay-to-delay (∞delay-to-Delay (inl tt , t))
  --     ≡⟨ {!!} ⟩
  --   (Delay-to-delay-later-x (later (delay-to-∞Delay (t tt)))) ,
  --   (Delay-to-delay-later-π (later (delay-to-∞Delay (t tt))))
  --     ≡⟨ {!!} ⟩ -- inl tt , λ _ → Delay-to-delay-later-x (force t) n
  --   ((λ (a , b) → (λ { 0 → lift tt ; (suc n) → (a .fst n) , (b .fst n)}) , λ { 0 → refl {x = lift tt} ; (suc m) i → a .snd m i , b .snd m i })
  --     (inv (compIso (Σ-ap-iso₂ (λ a,p →
  --          Σ-ap-iso (pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → cong (λ k → B k → W S n) (α-iso-step-5-Iso-helper0 {S = S} (a,p .fst) (a,p .snd) n)))) λ u →
  --                   pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → α-iso-step-5-Iso-helper1 {S = S} (a,p .fst) (a,p .snd) u n))))) (((inv (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x))) (inl tt) , subst ? (sym (fst (vogt (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x))) (inl tt))) ((λ n z → (t z) .fst n) , (λ n i a → (t a) .snd n i))))))
  --     ≡⟨ {!!} ⟩
  --   in-fun (inl tt , t) ∎})
  -- where
  --   postulate
  --     temp : ∀ t → (lift-x-general (λ n → inl tt) , lift-π-general (λ n → inl tt) (λ n _ → inl tt)) ≡ in-fun (inl tt , t)

-- delay-equality-Iso : ∀ {R : Set} -> Iso (delay R) (Delay R)
-- delay-equality-Iso = (iso delay-to-Delay Delay-to-delay delay-equality-section delay-equality-retraction)

-- delay-equality : ∀ {R : Set} -> delay R ≡ Delay R
-- delay-equality = isoToPath delay-equality-Iso

-- Bottom element raised
data ⊥₁ : Set₁ where

-- TREES
tree-S : (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ-suc ℓ-zero}
tree-S E R = (R ⊎ Σ Set (λ A -> E A)) , (λ { (inl _) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

tree : (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
tree E R = M (tree-S E R)

tree-ret : ∀ {E} {R}  -> R -> tree E R
tree-ret {E} {R} r = in-fun (inl r , λ ())

tree-vis : ∀ {E} {R}  -> ∀ {A} -> E A -> (A -> tree E R) -> tree E R
tree-vis {A = A} e k = in-fun (inr (A , e) , λ { (lift x) -> k x } )

-- ITREES

itree-S : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ-suc ℓ-zero}
itree-S E R = ((Unit ⊎ R) ⊎ Σ Set E) , (λ { (inl (inl _)) -> Lift Unit ; (inl (inr _)) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

itree :  ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
itree E R = M (itree-S E R)

ret' : ∀ {E} {R}  -> R -> P₀ {S = itree-S E R} (itree E R)
ret' {E} {R} r = inl (inr r) , λ ()

tau' : {E : Set₀ -> Set₁} -> {R : Set₀} -> itree E R -> P₀ {S = itree-S E R} (itree E R)
tau' t = inl (inl tt) , λ x → t

vis' : ∀ {E} {R}  -> ∀ {A : Set} -> E A -> (A -> itree E R) -> P₀ {S = itree-S E R} (itree E R)
vis' {A = A} e k = inr (A , e) , λ { (lift x) -> k x }

ret : ∀ {E} {R}  -> R -> itree E R
ret = in-fun ∘ ret'

tau : {E : Set₀ -> Set₁} -> {R : Set₀} -> itree E R -> itree E R
tau = in-fun ∘ tau'

vis : ∀ {E} {R}  -> ∀ {A : Set} -> E A -> (A -> itree E R) -> itree E R
vis {A = A} e = in-fun ∘ (vis' {A = A} e)

-- Bind operations
{-# TERMINATING #-}
bind-helper : ∀ {E : Set -> Set₁} {R S : Set} -> (R -> itree E S) -> P₀ {S = itree-S E R} (itree E R) -> itree E S
bind-helper k (inl (inl tt), b) = tau (bind-helper k (out-fun (b (lift tt))))
bind-helper k (inl (inr r), _) = k r
bind-helper k (inr (A , e), k') = vis e λ (x : A) → bind-helper k (out-fun (k' (lift x)))

bind : ∀ {E} {R} {S} -> itree E R -> (R -> itree E S) -> itree E S
bind {E} {R} {S} t k = bind-helper k (out-fun {S = itree-S E R} t)

syntax bind e₁ (λ x → e₂) = x ← e₁ , e₂

trigger : ∀ {E R} -> E R -> itree E R
trigger e = vis e λ x → ret x
