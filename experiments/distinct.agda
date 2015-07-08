{-# OPTIONS --without-K #-}
module distinct where

open import Type
open import Type.Identities
open import Algebra.FunctionProperties.Eq
              renaming (Injective to is-injective)
open import Function.NP
open import Function.Extensionality
open import Data.Fin.NP using (Fin; Fin▹ℕ; _==_)
open import Data.Vec.NP
open import Data.Vec.Properties
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Zero
open import Data.One
open import Data.Two hiding (_==_)
open import Data.Sum hiding (map)
open import Data.Nat.NP hiding (_==_)
open import Data.Nat.Properties
import Data.List as L
import Data.List.Properties as LP
open L using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality.NP
open import HoTT
open Equivalences
--open import Explore.Fin

is-distinct : {A : Set}{n : ℕ} → Vec A n → Set
is-distinct {n = n} v = is-injective (_‼_ v)
-- is-distinct {n = n} v = {p q : Fin n}(e : v ‼ p ≡ v ‼ q) → p ≡ q

Distinct : (A : Set)(n : ℕ) → Set
Distinct A n = Σ (Vec A n) is-distinct

Injection : (A B : Set) → Set
Injection A B = Σ (A → B) is-injective

Auto : (A : Set) → Set
Auto A = Injection A A

Perm : (n : ℕ) → Set
Perm n = Distinct (Fin n) n

module _ {n} {{_ : FunExt}} where
    Perm→Auto : Perm n → Auto (Fin n)
    Perm→Auto (v , v-dist) = _‼_ v , v-dist

    tabulate-dist : (f : Fin n → Fin n) (f-inj : Injective f) → is-distinct
    tabulate-dist f f-inj e = f-inj (! lookup∘tabulate f _ ∙ e ∙ lookup∘tabulate f _)

    Auto→Perm : Auto (Fin n) → Perm n
    Auto→Perm (f , f-inj)
      = tabulate f , λ e → f-inj (! lookup∘tabulate f _ ∙ e ∙ lookup∘tabulate f _)

Goal: tr is-injective (λ= (lookup∘tabulate f))
      (snd (Auto→Perm (f , f-inj)))
      ≡ f-inj
    Perm→Auto→Perm : ∀ a → Perm→Auto (Auto→Perm a) ≡ a
    Perm→Auto→Perm (f , f-inj) = pair= (λ= (lookup∘tabulate f)) {!!}

    Auto→Perm→Auto : ∀ π → Auto→Perm (Perm→Auto π) ≡ π
    Auto→Perm→Auto (v , v-dist) = pair= (tabulate∘lookup v) {!!}

    Perm≃Auto : Perm n ≃ Auto (Fin n)
    Perm≃Auto = equiv Perm→Auto Auto→Perm Perm→Auto→Perm Auto→Perm→Auto

Arr : (n : ℕ) → Set
Arr n = Vec (Fin n) n

Sum : Set → Set
Sum A = (A → ℕ) → ℕ
Prod = Sum

postulate
    sumFin : (n : ℕ) → Sum (Fin n)
    prodFin : (n : ℕ) → Prod (Fin n)
    -- sumVec : (A : Set)(n : ℕ) (f : Vec A n → ℕ) → ℕ
    sumArr : (n : ℕ) → Sum (Arr n)
    prodFinEq : {n : ℕ}(x y : Fin n) → Prod (x ≡ y)

distinctℕ : (n : ℕ) → (sumArr  n λ v →
                        prodFin n λ p →
                        prodFin n λ q → 
                        prodFinEq p q λ e →
                        𝟚▹ℕ (p == q)) ≡ {!!}
distinctℕ = {!!}

{-
ℕ< : ℕ → Set
ℕ< n = Σ ℕ λ x → x < n

sum< : (n : ℕ) (f : ℕ< n → ℕ) → ℕ
sum< n f = {!!}

prod< : (n : ℕ) (f : ℕ< n → ℕ) → ℕ
prod< n f = {!!}

{-
foo : ∀ n a x → sumFin n λ i → a i * x ^ i
foo = ?

bar : ∀ n a x → sumFin n λ i → a i * x ^ i
bar = ?
-}

baz : ∀ n (u : ℕ< n → ℕ) → (sum< n λ { (i , p) → prod< i (λ { (j , q) → u (j , <-trans q p) }) }) ≡ {!!}
baz = {!!}

module _ n (u : ℕ< n → Set) {{_ : UA}} {{_ : FunExt}} where
    open ≡-Reasoning
    Baz : _ ≡ _
    Baz = (Σ (ℕ< n) λ { (i , p) → Π (ℕ< i) λ { (j , q) → u (j , <-trans q p) } })
        ≡⟨ ! Σ-assoc ⟩
          (Σ ℕ λ i → Σ (i < n) λ p → Π (ℕ< i) λ { (j , q) → u (j , <-trans q p) })
        ≡⟨ Σ=′ ℕ (λ i → Σ=′ (i < n) λ p → ΠΣ-curry) ⟩
          (Σ ℕ λ i → Σ (i < n) λ p → Π ℕ λ j → Π (j < i) λ q → u (j , <-trans q p))
        ∎

module DataVersion (A : ★) where
    open import Data.Tree.Binary
    data T : BinTree A → ★ where
      empty : T empty
      _⊕_ : ∀ {t u} → (𝟙 ⊎ T t × T u) → T (fork t u)

module TypeVersion where
    ε = 𝟙
    _⊕_ : ★ → ★ → ★
    _⊕_ = λ u z → ε ⊎ u × z
    

module ListVersion where
    open L
    open ≡-Reasoning
    map-∘ = LP.map-compose

    sum-lin : ∀ k xs → sum (map (_*_ k) xs) ≡ k * sum xs
    sum-lin k []       = ℕ°.*-comm 0 k
    sum-lin k (x ∷ xs) = k * x + sum (map (_*_ k) xs)
                       ≡⟨ ap (_+_ (k * x)) (sum-lin k xs) ⟩
                          k * x + k * sum xs
                       ≡⟨ ! fst ℕ°.distrib k x (sum xs) ⟩
                          k * (x + sum xs)
                       ∎

    lemma : ∀ x xss → sum (map product (map (_∷_ x) xss)) ≡ x * sum (map product xss)
    lemma x xss = sum (map product (map (_∷_ x) xss))
                ≡⟨ ap sum (! map-∘ xss) ⟩
                  sum (map (product ∘ _∷_ x) xss)
                ≡⟨by-definition⟩
                  sum (map (_*_ x ∘ product) xss)
                ≡⟨ ap sum (map-∘ xss) ⟩
                  sum (map (_*_ x) (map product xss))
                ≡⟨ sum-lin x (map product xss) ⟩
                  x * sum (map product xss)
                ∎

    ε = 1
    _⊕_ = λ u z → ε + u * z
    t3 = ∀ xs → sum (map product (inits xs)) ≡ foldr _⊕_ ε xs
    t4 : t3
    t4 [] = refl
    t4 (x ∷ xs) = ap suc (lemma x (inits xs) ∙ ap (_*_ x) (t4 xs))
-- -}
-- -}
-- -}
-- -}
-- -}
