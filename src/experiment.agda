{-# OPTIONS --cubical --guardedness --safe #-} 

module experiment where

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to empty-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥)
open import Cubical.HITs.SetQuotients renaming (elim to elim/)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.HLevels
open import helper renaming (rec to rec/)

open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.Container

tree = M (ℕ , λ {_ → Unit ⊎ Unit})

value : tree → ℕ
value t = out-fun t .fst

left-child : tree → tree
left-child t = out-fun t .snd (inl tt)

right-child : tree → tree
right-child t = out-fun t .snd (inr tt)

-- Natural numbers?
data Un : Set where
  k : Un
  later : Un → Un

data _Un∼_ : Un → Un → Set where
  k∼ : k Un∼ k
  later∼ : ∀ {a b} → a Un∼ b → later a Un∼ later b
  eqL∼ : ∀ {a b} → a Un∼ b → later a Un∼ b
  eqR∼ : ∀ {a b} → a Un∼ b → a Un∼ later b
  
data Unit-type : Set where
  k : Unit-type
  later : Unit-type → Unit-type
  later-eq : ∀ {x y : Unit-type} → x ≡ y → later x ≡ y
  Unit-isSet : isSet Unit-type

fun : Un / _Un∼_ → Unit-type
fun = (λ x → rec/ (λ _ → k) (λ _ _ _ → refl) Unit-isSet x)

later-embedding : ∀ {R : Set} {a b : Unit-type} → (later a ≡ later b) ≡ (a ≡ b)
later-embedding {a = a} {b} =
  (later a ≡ later b)
    ≡⟨ cong (λ k → k ≡ later b) (later-eq refl) ⟩
  (a ≡ later b)
    ≡⟨ cong (λ k → a ≡ k) (later-eq refl) ⟩
  a ≡ b ∎

fun-≡→∼ : {x y : Un} → fun [ x ] ≡ fun [ y ] → x Un∼ y
fun-≡→∼ {k} {k} p = k∼
fun-≡→∼ {k} {later t} p = eqR∼ (fun-≡→∼ refl)
fun-≡→∼ {later t} {k} p = eqL∼ (fun-≡→∼ refl)
fun-≡→∼ {later t} {later u} p = later∼ (fun-≡→∼ refl)

fun-injective : isInjective fun
fun-injective {x} {w} =
  elimProp
    {A = Un}
    {R = _Un∼_}
    {B = λ x → fun x ≡ fun w → x ≡ w}
    (λ x → isPropΠ λ _ → squash/ x w)
    (λ a →
      elimProp
        {A = Un}
        {R = _Un∼_}
        {B = λ w → fun [ a ] ≡ fun w → [ a ] ≡ w}
        (λ w → isPropΠ λ _ → squash/ [ a ] w)
        (λ b → eq/ a b ∘ fun-≡→∼)
        w)
    x

elimPropUnit-type :
  ∀ (P : Unit-type → Set)
  → (∀ a → isProp (P a))
  → (P k)
  → (∀ t → P t → P (later t))
  → (x : Unit-type) → P x
elimPropUnit-type P Pprop pn Pl = temp
  where
    temp : (x : Unit-type) → P x
    temp k = pn 
    temp (later x) = Pl x (temp x)
    temp (later-eq {t} {u} p i) =
      isOfHLevel→isOfHLevelDep 1 Pprop (Pl t (temp t)) (temp u) (later-eq {t} {u} p) i
    temp (Unit-isSet a b p q i j) =
      isOfHLevel→isOfHLevelDep 2 (isProp→isSet ∘ Pprop) ((temp) a) ((temp) b) (cong (temp) p) (cong (temp) q) (Unit-isSet a b p q) i j

fun-surjective-pre : isSurjection (fun ∘ [_])
fun-surjective-pre =
  elimPropUnit-type
    (λ x → ∥ fiber (fun ∘ [_]) x ∥)
    (λ _ → propTruncIsProp)
    (∣ k , refl ∣)
    (λ t → ∥map∥ (λ x → later (x .fst) , ((fun ∘ [_]) (later (x .fst)) ≡⟨ x .snd ⟩ t ≡⟨ sym (later-eq refl) ⟩ later t ∎))) 

fun-surjective : isSurjection fun
fun-surjective x =
  ∥map∥ (λ {(x , y) → [ x ] , y}) (fun-surjective-pre x)
  
asdf : Un / _Un∼_ ≡ Unit-type
asdf = ua (fun , isEmbedding×isSurjection→isEquiv (injEmbedding squash/ Unit-isSet fun-injective , fun-surjective))

ha' : Unit-type ≡ Unit
ha' = isoToPath (iso (λ x → tt) (λ _ → k) (λ b → refl) (elimPropUnit-type (λ x → k ≡ x) (Unit-isSet k) refl (λ t p → sym (later-eq (sym p)))))
