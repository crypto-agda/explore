{-# OPTIONS --without-K #-}
open import Function
open import Data.Zero
open import Relation.Binary.PropositionalEquality.NP
open import Explore.Zero
import Explore.Universe.Type
import Explore.Universe
open import Function.Extensionality
open import Type.Identities
open import HoTT
open Equivalences

module Explore.Universe.Base
  (open Explore.Universe.Type {𝟘})
  (u : U) where

open Explore.Universe 𝟘

open FromKit 𝟘ⁱ (λ {{ua}}{{_}} → 𝟘ˢ-ok {{ua}}) 𝟘ˡ 𝟘ᶠ
             (λ {{ua}} → Σᵉ𝟘-ok {{ua}})
             Πᵉ𝟘-ok (λ {ℓ₀ ℓ₁} ℓᵣ → ⟦𝟘ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} {_≡_})
             (const 𝟙ᵁ) (λ {{ua}} {{fext}} v → equiv (λ _ ()) _ (λ f → λ= (λ())) (λ _ → refl))
             u public
