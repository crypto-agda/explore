{-# OPTIONS --without-K #-}
open import Data.Nat
open import Data.Two
open import Data.Zero
open import Data.Fin.NP
open import Type
open import Function
open import Relation.Binary.PropositionalEquality.NP

import Explore.Universe.Base
open import Explore.Core
open import Explore.Zero
open import Explore.One
open import Explore.Two
open import Explore.Universe.Type

-- Exploring Fin comes in two flavors Regular & Custom
-- We recommend Regular if you want to work for arbitrary values of n.
-- We recommend Custom if you want to work for particular values of n (2, 6...).
module Explore.Fin where

module Regular n = Explore.Universe.Base (≃ᵁ (Finᵁ n) (Fin n) (Finᵁ≃Fin n))

module Custom where
  module _ n where
    open Explore.Universe.Base (≃ᵁ (Finᵁ' n) (Fin n) (Finᵁ'≃Fin n))
      public

  Finᵉ0-𝟘ᵉ : (λ {M : ★₀} (ε : M) op f → explore 0 ε op (f ∘ Fin▹𝟘)) ≡ 𝟘ᵉ
  Finᵉ0-𝟘ᵉ = refl

  Finᵉ1-𝟙ᵉ : (λ {M : ★₀} (ε : M) op f → explore 1 ε op (f ∘ Fin▹𝟙)) ≡ 𝟙ᵉ
  Finᵉ1-𝟙ᵉ = refl

  Finᵉ2-𝟚ᵉ : (λ {M : ★₀} (ε : M) op f → explore 2 ε op (f ∘ Fin▹𝟚)) ≡ 𝟚ᵉ
  Finᵉ2-𝟚ᵉ = refl

module ByHand {ℓ} where
  Finᵉ' : ∀ n → Explore ℓ (Fin n)
  Finᵉ' zero    z _⊕_ f = z
  Finᵉ' (suc n) z _⊕_ f = f zero ⊕ Finᵉ' n z _⊕_ (f ∘ suc)

  -- Finᵉ and Finᵉ' are extensionally equal.
  -- Moreover the simplicity of the proof shows that the two functions are computing
  -- in the same way.
  Finᵉ-Finᵉ' : ∀ n {M} (ε : M) (_⊕_ : M → M → M) (f : Fin n → M) → Regular.explore n ε _⊕_ f ≡ Finᵉ' n ε _⊕_ f
  Finᵉ-Finᵉ' zero    ε _⊕_ f = idp
  Finᵉ-Finᵉ' (suc n) ε _⊕_ f = ap (_⊕_ (f zero))
                                  (Finᵉ-Finᵉ' n ε _⊕_ (f ∘ suc))
