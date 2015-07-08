{-# OPTIONS --without-K #-}
module horner where

open import Type
open import Type.Identities
open import Function.NP
open import Function.Extensionality
open import Data.Fin.NP using (Fin; Fin▹ℕ)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Zero
open import Data.One
open import Data.Sum hiding (map)
open import Data.Nat.NP
open import Data.Nat.Properties
import Data.List as L
import Data.List.Properties as LP
open L using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality.NP
open import HoTT
--open import Explore.Fin

ℕ< : ℕ → Set
ℕ< n = Σ ℕ λ x → x < n

sumFin : (n : ℕ) (f : Fin n → ℕ) → ℕ
sumFin n f = {!!}

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
