{-# OPTIONS --without-K #-}
open import Data.Zero
open import Relation.Binary.PropositionalEquality.NP
open import Explore.Zero
open import Explore.Universe.Type

module Explore.Universe.Base (u : U {𝟘}) where

open import Explore.Universe 𝟘

open FromKit 𝟘ⁱ (λ {{ua}}{{_}} → 𝟘ˢ-ok {{ua}}) 𝟘ˡ 𝟘ᶠ
             (λ {{ua}} → Σᵉ𝟘-ok {{ua}})
             Πᵉ𝟘-ok (λ {ℓ₀ ℓ₁} ℓᵣ → ⟦𝟘ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} {_≡_}) u public
