{-# OPTIONS --without-K #-}
-- Unfinished


open import Type
open import Function.NP
open import Data.Nat
open import Data.Product
open import Data.Fin using (Fin)
open import Explore.Type
import Function.Related as FR
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import Function.Related.TypeIsomorphisms.NP

module Explore.BigDistr
                {A B : ★₀}
                {exploreᴬ : Explore₀ A} 
                {exploreᴮ : Explore₀ B} 
                {exploreᴬᴮ : Explore₀ (A → B)}
                (F : A → B → ℕ)
                where
  productᴬ = exploreᴬ _*_
  sumᴮ = exploreᴮ _+_
  sumᴬᴮ = exploreᴬᴮ _+_

  module _
    (adequate-productᴬ : AdequateProduct productᴬ)
    (adequate-sumᴮ : AdequateSum sumᴮ)
    (adequate-sumᴬᴮ : AdequateSum sumᴬᴮ)
    where

    open FR.EquationalReasoning
    big-distr :
      productᴬ (sumᴮ ∘ F) ≡
      sumᴬᴮ (λ f → productᴬ (F ˢ f))
    big-distr = Fin-injective (
        Fin (productᴬ (sumᴮ ∘ F))
      ↔⟨ adequate-productᴬ (sumᴮ ∘ F) ⟩
        Π A (Fin ∘ sumᴮ ∘ F)
      ↔⟨ {!!} ⟩
        Π A (λ x → Σ B (Fin ∘ F x))
      ↔⟨ dep-choice-iso _ ⟩
        Σ (Π A (const B)) (λ f → Π A (λ x → Fin (F x (f x))))
      ↔⟨ second-iso (λ f → sym (adequate-productᴬ (F ˢ f))) ⟩
        Σ (Π A (const B)) (λ f → Fin (productᴬ (F ˢ f)))
      ↔⟨ sym (adequate-sumᴬᴮ (λ f → productᴬ (F ˢ f))) ⟩
        Fin (sumᴬᴮ (λ f → productᴬ (F ˢ f)))
      ∎)
