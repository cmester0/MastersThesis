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

open import Container
open import M
open import Coalg
open import helper

open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Foundations.Embedding

module itree where

delay-helper : ∀ (R : Set) → (Unit ⊎ R) → Set
delay-helper R (inr _) = ⊥
delay-helper R (inl tt) = Unit

-- itrees (and buildup examples)
delay-S : (R : Set₀) -> Container
delay-S R = (Unit ⊎ R) , delay-helper R

delay : (R : Set₀) -> Set₀
delay R = M (delay-S R)

delay-ret : {R : Set} -> R -> delay R
delay-ret r = in-fun (inr r , λ ())

delay-tau : {R : Set₀} -> delay R -> delay R
delay-tau t = in-fun (inl tt , λ _ → t)

inr-inj : ∀ {ℓ} {M : Set ℓ} {R : Set ℓ} (a b : R) → (inr {A = M} {B = R} a ≡ inr b) ≡ (a ≡ b) ⊎ ⊥
inr-inj a b =
  (sym (ua (SumPath.Cover≃Path (inr a) (inr b)))) □ isoToPath (iso (inl ∘ lower) (λ {(inl x) → lift x ; (inr ())}) (λ {(inl x) → refl ; (inr ())}) refl-fun)

-- inr-inj-unit : ∀ {R : Set} (a b : R) → (inr {A = Unit} {B = R} a ≡ inr b) ≡ (a ≡ b)
-- inr-inj-unit a b =
--   (sym (ua (SumPath.Cover≃Path (inr a) (inr b)))) □ isoToPath (iso lower lift refl-fun refl-fun)

-- inr-inj' : ∀ {ℓ} {M : Set ℓ} {R : Set ℓ} (a : R) → isContr (a ≡ a) → (p : inr {A = M} {B = R} a ≡ inr a) → ∀ i → p i ≡ inr a
-- inr-inj' a x p i =
--   p i
--     ≡⟨ {!!} ⟩
--   inr ((case transport (inr-inj a a) p return (λ x₁ → a ≡ a) of λ {(inl k) → k ; (inr ())}) i)
--     ≡⟨ cong inr {!!} ⟩
--   inr a ∎

helper-missing-5 : ∀ {R : Set} (a b : R) → (p : inr {A = Unit} a ≡ inr b)
  → cong (inr {A = Unit}) (transport (inr-inj-unit a b) p)
  ≡ cong (inr {A = Unit}) (transport (inr-inj-unit a b) (cong (inr {A = Unit}) (transport (inr-inj-unit a b) p)))
helper-missing-5 = {!!}

helper-missing-4 : ∀ {R : Set} (a b : R) → isEmbedding (λ (p : inr {A = Unit} a ≡ inr b) → cong (inr {A = Unit}) (transport (inr-inj-unit a b) p))
helper-missing-4 a b w x = {!!}

helper-missing : ∀ {R : Set} (a b : R) → (p : inr {A = Unit} a ≡ inr b) → p ≡ cong inr (transport (inr-inj-unit a b) p)
helper-missing a b p = helper-missing-4 a b p (cong inr (transport (inr-inj-unit a b) p)) .equiv-proof (helper-missing-5 a b p) .fst .fst

-- TODO: Combine the two proofs for delay-ret and delay-tau, since they are part of the same property for in-fun, splitting this property makes the proof harder!
delay-ret-inj : ∀ R (a b : R) → (delay-ret a ≡ delay-ret b) ≡ (a ≡ b)
delay-ret-inj R a b = 
  delay-ret a ≡ delay-ret b
    ≡⟨ refl ⟩
  in-fun (inr a , λ ()) ≡ in-fun (inr b , λ ())
    ≡⟨ in-inj-x ⟩
  (inr a , λ ()) ≡ (inr b , λ ())
    ≡⟨ sym Σ-split ⟩
  (Σ (inr a ≡ inr b) λ y → PathP (λ x → delay-helper R (y x) → M ((Unit ⊎ R) , delay-helper R)) _ _)
    -- ≡⟨ Σ-ap (inr-inj-unit a b) (λ y → cong (λ k → PathP (λ x → delay-helper R ((k y) x) → M ((Unit ⊎ R) , delay-helper R)) _ _) (funExt (helper-missing {R = R} a b))) ⟩
    ≡⟨ Σ-ap (inr-inj-unit a b) (λ y → cong (λ k → PathP (λ x → delay-helper R ((k y) x) → M ((Unit ⊎ R) , delay-helper R)) _ _) (λ i → transp (λ j → {!!}) i y)) ⟩
  (Σ ((a ≡ b)) λ y → PathP (λ x → delay-helper R (transport (sym (inr-inj-unit a b)) y x) → M ((Unit ⊎ R) , delay-helper R)) _ _)
    ≡⟨ refl ⟩
  (Σ ((a ≡ b)) λ y → PathP (λ x → delay-helper R (inr (y x)) → M ((Unit ⊎ R) , delay-helper R)) _ _)
    ≡⟨ {!!} ⟩
  (Σ ((a ≡ b)) λ y → Lift Unit)
    ≡⟨ {!!} ⟩
  (a ≡ b) ∎

-- (λ i → transp (λ j → inr-inj-unit a b j) i y)
-- Σ-ap (inr-inj-unit a b) (λ y → cong (λ k → PathP (λ x → delay-helper R (k x) → M ((Unit ⊎ R) , delay-helper R)) _ _) (transp {!!} {!!} y))

-- pair-contracitve : ∀ (R : Set) → ∀ (a b : Unit ⊎ R) → (p : a ≡ b) → isContr (SumPath.Cover {A = Unit} {B = R} a b)
-- pair-contracitve R (inl tt) (inl tt) p = lift refl , λ y i → lift refl
-- pair-contracitve R (inl tt) (inr s) p = {!!}
-- pair-contracitve R (inr r) (inl tt) p = {!!}
-- pair-contracitve R (inr r) (inr s) p = lift (case transport (inr-inj r s) p return (λ _ → r ≡ s) of (λ {(inl x) → x ; (inr ())})) , λ y i → lift {!!}

-- isContr→isContr-≡ : ∀ {A} → isContr A → isContr (A ≡ A)
-- isContr→isContr-≡ {A} x = (λ i → A) , λ y i → {!!}

-- postulate
--   isContr→isContr-≡ : ∀ {A} → isContr A → isContr (A ≡ A)

-- unit-interval : isContr (Unit ≡ Unit)
-- unit-interval = {!!}

-- isEmbedding-delay-helper : ∀ {R : Set} → isEmbedding (delay-helper R)
-- isEmbedding-delay-helper {R} (inl tt) (inl tt) = record { equiv-proof = λ y → (refl , λ i → isContr→isProp unit-interval refl y i) , {!!} }
-- isEmbedding-delay-helper (inl tt) (inr s) = {!!}
-- isEmbedding-delay-helper (inr r) (inl tt) = {!!}
-- isEmbedding-delay-helper (inr r) (inr s) = {!!}

-- isEmbedding-delay-tau : ∀ {R : Set} → isEmbedding (delay-tau {R = R})
-- isEmbedding-delay-tau w z = {!!}

-- -- snd (compEquiv LiftEquiv (SumPath.Cover≃Path (inr w) (inr z)))

-- inr-inj : ∀ {ℓ} {M : Set ℓ} {R : Set ℓ} (a b : R) → (inr {A = M} {B = R} a ≡ inr b) ≡ (a ≡ b) ⊎ ⊥
-- inr-inj a b =
--   (sym (ua (SumPath.Cover≃Path (inr a) (inr b)))) □ isoToPath (iso (inl ∘ lower) (λ {(inl x) → lift x ; (inr ())}) (λ {(inl x) → refl ; (inr ())}) refl-fun)

-- inl-inj : ∀ {ℓ} {M : Set ℓ} {R : Set ℓ} (a b : R) → (inl {A = R} {B = M} a ≡ inl b) ≡ (a ≡ b) ⊎ ⊥
-- inl-inj a b =
--   (sym (ua (SumPath.Cover≃Path (inl a) (inl b)))) □ isoToPath (iso (inl ∘ lower) (λ {(inl x) → lift x ; (inr ())}) (λ {(inl x) → refl ; (inr ())}) refl-fun)


-- -- sdfafads : ∀ {ℓ} (M R : Set ℓ) (r : R) → (p : inr {A = M} r ≡ inr r) → ∀ (i : I) → (p i ≡ r)
-- -- sdfafads M R r s x y = {!!}

-- asdf : ∀ R r s → (p : inr r ≡ inr s) → (q : r ≡ s) → (∀ i → (delay-helper R (p i) ≡ delay-helper R (p i)) ≡ (delay-helper R (inr (q i)) ≡ delay-helper R (inr (q i))))
-- asdf R r s p q i = isoToPath (iso (λ x → {!!}) {!!} {!!} {!!})

-- asdf2 : ∀ R r s → delay-helper R (inl r) ≡ delay-helper R (inl s)
-- asdf2 R r s = refl

-- delay-tau-inj : ∀ {R} t u → (delay-tau {R = R} t ≡ delay-tau u) ≡ (t ≡ u)
-- delay-tau-inj {R = R} t u =
--   delay-tau t ≡ delay-tau u
--     ≡⟨ in-inj-x ⟩
--   (inl tt , λ (_ : Unit) → t) ≡ (inl tt , λ (_ : Unit) → u)
--     ≡⟨ sym Σ-split-iso ⟩
--   Σ (inl tt ≡ inl tt) (λ q → PathP (λ i → delay-helper R (q i) → M ((Unit ⊎ R) , delay-helper R)) (λ (_ : Unit) → t) (λ (_ : Unit) → u))
--     ≡⟨ isoToPath (iso (λ x → λ i x₁ → x .snd i (transport
--       (Unit
--         ≡⟨ refl ⟩
--       delay-helper R (inl tt)
--         ≡⟨ {!!} ⟩
--       delay-helper R (inl (transport (case inl-inj tt tt of λ x₂ → refl) (fst x) i))
--         ≡⟨ {!!} ⟩
--       delay-helper R (fst x i) ∎) x₁))
--                       (λ x → refl , x)
--                       refl-fun
--                       {!!}) ⟩
--   (λ (_ : Unit) → t) ≡ (λ (_ : Unit) → u)
--     ≡⟨ {!!} ⟩
--   t ≡ u ∎

-- delay-constructor-inj : ∀ {R} a b c d → (in-fun {S = delay-S R} (a , b) ≡ in-fun (c , d)) ≡ Σ (a ≡ c) (λ q → PathP (λ i → delay-S R .snd (q i) → M (delay-S R)) b d)
-- delay-constructor-inj {R} a b c d =
--   in-fun {S = delay-S R} (a , b) ≡ in-fun (c , d)
--     ≡⟨ in-inj-x ⟩
--   (a , b) ≡ (c , d)
--     ≡⟨ sym Σ-split-iso ⟩
--   Σ (a ≡ c) (λ q → PathP (λ i → delay-S R .snd (q i) → M (delay-S R)) b d) ∎ -- (Σ (a ≡ c) (λ q → PathP (λ i → B (q i)) b d)) = a , b = a' , b'

-- -- postulate
--   -- inr-inj : ∀ {R : Set} (a b : R) → (inr {A = Unit} a ≡ inr b) ≡ (a ≡ b) -- should follow from inr being an embedding!
--   -- empty-fun-is-unit : ∀ {A B : Set} (a b : A) -> (_≡_ {A = Σ (Unit ⊎ A) λ x → delay-helper A x} (inr a , λ ()) (inr b , λ ())) ≡ (inr {A = Unit} a ≡ inr b)
--   -- proof should be: isoToPath (iso (λ x i → x i .fst) (λ x → cong (λ a₁ → a₁ , λ ()) x) (λ b₁ → refl) λ a₁ → refl)
-- -- Error message:
-- -- (λ { (inr _) → ⊥ ; (inl tt) → Unit }) a₁ should be empty, but
-- -- that's not obvious to me
-- -- when checking that the expression λ () has type
-- -- (λ { (inr _) → ⊥ ; (inl tt) → Unit }) a₁ →
-- -- M ((Unit ⊎ R) , (λ { (inr _) → ⊥ ; (inl tt) → Unit }))

-- -- PathPIsContrUnit : ∀ A b c → isContr b → (PathP (λ i → A i) b c ≡ Lift Unit)
-- -- PathPIsContrUnit  A b c con = {!!}

-- isProp⊥→A : forall {i} {A : Set i} -> isProp (⊥ -> A)
-- isProp⊥→A x y = (sym (isContr⊥→A .snd x) □ isContr⊥→A .snd y)

-- isPropIsUnit : forall {i} {A : Set i} -> isProp (A) -> (x y : A) -> (x ≡ y) ≡ Lift Unit
-- isPropIsUnit p x y = isoToPath (iso (λ x₁ → lift tt)
--                                     (λ x₁ → p x y)
--                                     (λ b → refl)
--                                     λ a → isProp→isSet p x y (p x y) a)

-- ΣisProp : forall {i j} (A : Set i) (B : Set j) -> isProp A -> isProp B -> isProp (A ×Σ B)
-- ΣisProp A B a b x y = λ i → (a (x .fst) (y .fst) i) , (b (x .snd) (y .snd) i)

-- -- -- TODO: Combine the two proofs for delay-ret and delay-tau, since they are part of the same property for in-fun, splitting this property makes the proof harder!
-- -- delay-ret-inj : ∀ R (a b : R) → (delay-ret a ≡ delay-ret b) ≡ (a ≡ b)
-- -- delay-ret-inj R a b =
-- --   delay-ret a ≡ delay-ret b
-- --     ≡⟨ refl ⟩
-- --   in-fun (inr a , λ ()) ≡ in-fun (inr b , λ ())
-- --     ≡⟨ in-inj-x ⟩
-- --   (inr a , λ ()) ≡ (inr b , λ ())
-- --     ≡⟨ sym Σ-split-iso ⟩
-- --   (Σ (inr a ≡ inr b) λ y → PathP (λ x → delay-helper R (y x) → M ((Unit ⊎ R) , delay-helper R)) _ _)
-- --     ≡⟨ Σ-ap-iso (inr-inj a b) (λ y → \i -> PathP (λ x → delay-helper R (y i) → M ((Unit ⊎ R) , delay-helper R)) _ _) ⟩
-- --   {!!} -- (Σ ((a ≡ b)) λ y → PathP (λ x → delay-helper R (transport (sym (inr-inj a b)) y x) → M ((Unit ⊎ R) , delay-helper R)) _ _)
-- --     ≡⟨ {!!} ⟩
-- --   (Σ ((a ≡ b)) λ y → Lift Unit)
-- --     ≡⟨ {!!} ⟩
-- --   (a ≡ b) ∎

-- -- Contr→Equiv

-- -- Bottom element raised
-- data ⊥₁ : Set₁ where

-- -- TREES
-- tree-S : (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ-suc ℓ-zero}
-- tree-S E R = (R ⊎ Σ Set (λ A -> E A)) , (λ { (inl _) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

-- tree : (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
-- tree E R = M (tree-S E R)

-- tree-ret : ∀ {E} {R}  -> R -> tree E R
-- tree-ret {E} {R} r = in-fun (inl r , λ ())

-- tree-vis : ∀ {E} {R}  -> ∀ {A} -> E A -> (A -> tree E R) -> tree E R
-- tree-vis {A = A} e k = in-fun (inr (A , e) , λ { (lift x) -> k x } )

-- -- ITREES

-- itree-S : ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Container {ℓ-suc ℓ-zero}
-- itree-S E R = ((Unit ⊎ R) ⊎ Σ Set E) , (λ { (inl (inl _)) -> Lift Unit ; (inl (inr _)) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

-- itree :  ∀ (E : Set₀ -> Set₁) (R : Set₀) -> Set₁
-- itree E R = M (itree-S E R)

-- ret' : ∀ {E} {R}  -> R -> P₀ {S = itree-S E R} (itree E R)
-- ret' {E} {R} r = inl (inr r) , λ ()

-- tau' : {E : Set₀ -> Set₁} -> {R : Set₀} -> itree E R -> P₀ {S = itree-S E R} (itree E R)
-- tau' t = inl (inl tt) , λ x → t

-- vis' : ∀ {E} {R}  -> ∀ {A : Set} -> E A -> (A -> itree E R) -> P₀ {S = itree-S E R} (itree E R)
-- vis' {A = A} e k = inr (A , e) , λ { (lift x) -> k x }

-- ret : ∀ {E} {R}  -> R -> itree E R
-- ret = in-fun ∘ ret'

-- tau : {E : Set₀ -> Set₁} -> {R : Set₀} -> itree E R -> itree E R
-- tau = in-fun ∘ tau'

-- vis : ∀ {E} {R}  -> ∀ {A : Set} -> E A -> (A -> itree E R) -> itree E R
-- vis {A = A} e = in-fun ∘ (vis' {A = A} e)

-- -- Bind operations
-- {-# TERMINATING #-}
-- bind-helper : ∀ {E : Set -> Set₁} {R S : Set} -> (R -> itree E S) -> P₀ {S = itree-S E R} (itree E R) -> itree E S
-- bind-helper k (inl (inl tt), b) = tau (bind-helper k (out-fun (b (lift tt))))
-- bind-helper k (inl (inr r), _) = k r
-- bind-helper k (inr (A , e), k') = vis e λ (x : A) → bind-helper k (out-fun (k' (lift x)))

-- bind : ∀ {E} {R} {S} -> itree E R -> (R -> itree E S) -> itree E S
-- bind {E} {R} {S} t k = bind-helper k (out-fun {S = itree-S E R} t)

-- syntax bind e₁ (λ x → e₂) = x ← e₁ , e₂

-- trigger : ∀ {E R} -> E R -> itree E R
-- trigger e = vis e λ x → ret x
