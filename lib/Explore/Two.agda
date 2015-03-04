{-# OPTIONS --without-K #-}
open import Type
open import Type.Identities
open import Level.NP
open import Data.Two
open import Function
open import Function.Extensionality
open import Data.Product
open import Data.Sum
open import Data.Fin
open import Relation.Binary.PropositionalEquality.NP using (_≡_; refl; !_; _∙_)
open import Relation.Binary.Sum
open import HoTT

open import Explore.Sum
open import Explore.Core
open import Explore.Properties
open import Explore.Explorable

module Explore.Two where


module _ {ℓ} where
    𝟚ᵉ : Explore ℓ 𝟚
    𝟚ᵉ _ _∙_ f = f 0₂ ∙ f 1₂

    𝟚ⁱ : ∀ {p} → ExploreInd p 𝟚ᵉ
    𝟚ⁱ _ _ _P∙_ Pf = Pf 0₂ P∙ Pf 1₂

module _ {ℓ₁ ℓ₂ ℓᵣ} {R : 𝟚 → 𝟚 → ★₀} {r0 : R 0₂ 0₂}{r1 : R 1₂ 1₂} where
    ⟦𝟚ᵉ⟧ : ⟦Explore⟧ {ℓ₁} {ℓ₂} ℓᵣ R 𝟚ᵉ 𝟚ᵉ
    ⟦𝟚ᵉ⟧ _ _ _∙ᵣ_ fᵣ = fᵣ r0 ∙ᵣ fᵣ r1

module 𝟚ⁱ = FromExploreInd 𝟚ⁱ
open 𝟚ⁱ public using ()
  renaming (sum to 𝟚ˢ
           ;product to 𝟚ᵖ
           ;reify to 𝟚ʳ
           ;unfocus to 𝟚ᵘ
           )

module _ {ℓ} where
    module _ {{_ : UA}}{{_ : FunExt}} where
        Σᵉ𝟚-ok : Adequate-Σ {ℓ} (Σᵉ 𝟚ᵉ)
        Σᵉ𝟚-ok _ = ! Σ𝟚-⊎

        Πᵉ𝟚-ok : Adequate-Π {ℓ} (Πᵉ 𝟚ᵉ)
        Πᵉ𝟚-ok _ = ! Π𝟚-×

    𝟚ˡ : Lookup {ℓ} 𝟚ᵉ
    𝟚ˡ = proj

    𝟚ᶠ : Focus {ℓ} 𝟚ᵉ
    𝟚ᶠ (0₂ , x) = inj₁ x
    𝟚ᶠ (1₂ , x) = inj₂ x

explore𝟚     = 𝟚ᵉ
explore𝟚-ind = 𝟚ⁱ
lookup𝟚      = 𝟚ˡ
reify𝟚       = 𝟚ʳ
focus𝟚       = 𝟚ᶠ
unfocus𝟚     = 𝟚ᵘ
sum𝟚         = 𝟚ˢ

module _ {{_ : UA}}{{_ : FunExt}} where
    𝟚ˢ-ok : Adequate-sum 𝟚ˢ
    𝟚ˢ-ok f = ! (Σ𝟚-⊎ ∙ Fin-⊎-+)
