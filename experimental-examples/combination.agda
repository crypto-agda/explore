{-# OPTIONS --without-K #-}
module combination where

open import Type
open import Data.Nat.NP
open import Data.Nat.DivMod
open import Data.Fin using (Fin; Fin′; zero; suc) renaming (toℕ to Fin▹ℕ)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Sum
open import Data.Product
open import Data.Vec
open import Function.NP
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as Inv
open Inv using (_↔_; sym; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from; id to idI; _∘_ to _∘I_)
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.Sum
import Relation.Binary.PropositionalEquality as ≡

open import factorial

_/_ : ℕ → ℕ → ℕ
x / y = _div_ x y {{!!}}

module v0 where

  C : ℕ → ℕ → ℕ
  C n       zero    = 1
  C zero    (suc k) = 0
  C (suc n) (suc k) = C n k + C n (suc k)

  D : ℕ → ℕ → ★
  D n       zero    = 𝟙
  D zero    (suc k) = 𝟘
  D (suc n) (suc k) = D n k ⊎ D n (suc k)

  FinC≅D : ∀ n k → Fin (C n k) ↔ D n k
  FinC≅D n       zero    = Fin1↔𝟙
  FinC≅D zero    (suc k) = Fin0↔𝟘
  FinC≅D (suc n) (suc k) =  FinC≅D n k ⊎-cong FinC≅D n (suc k)
                         ∘I sym (Fin-⊎-+ (C n k) (C n (suc k)))

module v! where

  C : ℕ → ℕ → ℕ
  C n k = n ! / (k ! * (n ∸ k)!)

module v1 where

  C : ℕ → ℕ → ℕ
  C n 0 = 1
  C n (suc k) = (C n k * (n ∸ k)) / suc k

module v2 where

  C : ℕ → ℕ → ℕ
  C n       zero    = 1
  C zero    (suc k) = 0
  C (suc n) (suc k) = (C n k * suc n) / suc k


{- Σ_{0≤k<n} (C n k) ≡ 2ⁿ -}

Σ𝟙F↔F : ∀ (F : 𝟙 → ★) → Σ 𝟙 F ↔ F _
Σ𝟙F↔F F = inverses proj₂ ,_ (λ _ → ≡.refl) (λ _ → ≡.refl)

Bits = Vec 𝟚
Bits1↔𝟚 : Bits 1 ↔ 𝟚
Bits1↔𝟚 = {!!}

open v0
foo : ∀ n → Σ (Fin (suc n)) (D (suc n) ∘ Fin▹ℕ) ↔ Bits (suc n)
foo zero = ((sym Bits1↔𝟚 ∘I {!!}) ∘I Σ𝟙F↔F _) ∘I first-iso Fin1↔𝟙
foo (suc n) = {!!}
