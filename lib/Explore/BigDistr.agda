{-# OPTIONS --without-K #-}
-- Lifting the dependent axiom of choice to sums and products

open import Type
open import Function.NP
open import Function.Extensionality
open import Data.Nat
open import Data.Product
open import Data.Fin using (Fin)
open import Explore.Core
open import Explore.Properties
open import Relation.Binary.PropositionalEquality.NP
open import Type.Identities
open import HoTT
open ≡-Reasoning
open Adequacy _≡_

module Explore.BigDistr
                {A B          : ★₀}
                {Πᴬ           : Product A}
                (adequate-Πᴬ  : Adequate-product Πᴬ)
                {Σᴮ           : Sum B}
                (adequate-Σᴮ  : Adequate-sum Σᴮ)
                {Σᴬᴮ          : Sum (A → B)}
                (adequate-Σᴬᴮ : Adequate-sum Σᴬᴮ)
                (F            : A → B → ℕ)
                {{_           : UA}}
                {{_           : FunExt}}
                where

big-distr : Πᴬ (Σᴮ ∘ F) ≡ Σᴬᴮ λ f → Πᴬ (F ˢ f)
big-distr =
  Fin-injective
  ( Fin (Πᴬ (Σᴮ ∘ F))
  ≡⟨ adequate-Πᴬ (Σᴮ ∘ F) ⟩
    Π A (Fin ∘ Σᴮ ∘ F)
  ≡⟨ Π=′ A (adequate-Σᴮ ∘ F) ⟩
    Π A (λ x → Σ B (Fin ∘ F x))
  ≡⟨ ΠΣ-comm ⟩
    Σ (Π A (const B)) (λ f → Π A (λ x → Fin (F x (f x))))
  ≡⟨ Σ=′ (A → B) (λ f → ! (adequate-Πᴬ (F ˢ f))) ⟩
    Σ (A → B) (λ f → Fin (Πᴬ (F ˢ f)))
  ≡⟨ ! (adequate-Σᴬᴮ (λ f → Πᴬ (F ˢ f))) ⟩
    Fin (Σᴬᴮ (λ f → Πᴬ (F ˢ f)))
  ∎)
