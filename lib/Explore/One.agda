open import Type
open import Type.Identities
open import Level.NP
open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
open import Data.One
open import Data.Fin
open import Function.NP
open import Data.Product
open import HoTT
open import Relation.Binary.PropositionalEquality.NP using (refl; _≡_; !_)
import Explore.Monad

module Explore.One where


module _ {ℓ} where
    open Explore.Monad ℓ

    𝟙ᵉ : Explore ℓ 𝟙
    𝟙ᵉ = return _
    {- or
    𝟙ᵉ _ f = f _
    -}

    𝟙ⁱ : ∀ {p} → ExploreInd p 𝟙ᵉ
    𝟙ⁱ = return-ind _
    {- or
    𝟙ⁱ _ _ Pf = Pf _
    -}

module _ {ℓ₁ ℓ₂ ℓᵣ} {R : 𝟙 → 𝟙 → ★₀} {r : R _ _} where
    ⟦𝟙ᵉ⟧ : ⟦Explore⟧ᵤ ℓ₁ ℓ₂ ℓᵣ R 𝟙ᵉ 𝟙ᵉ
    ⟦𝟙ᵉ⟧ _ _ _∙ᵣ_ fᵣ = fᵣ r

open Explorable₀ 𝟙ⁱ public using () renaming (sum to 𝟙ˢ; product to 𝟙ᵖ)

module _ {{_ : UA}} where
    Σᵉ𝟙-ok : ∀ {ℓ} → Adequate-Σᵉ {ℓ} 𝟙ᵉ
    Σᵉ𝟙-ok _ = ! Σ𝟙-snd

    Πᵉ𝟙-ok : ∀ {ℓ} → Adequate-Πᵉ {ℓ} 𝟙ᵉ
    Πᵉ𝟙-ok _ = ! Π𝟙-uniq _

    𝟙ˢ-ok : Adequate-sum 𝟙ˢ
    𝟙ˢ-ok _ = ! 𝟙×-snd

    𝟙ᵖ-ok : Adequate-product 𝟙ᵖ
    𝟙ᵖ-ok _ = ! Π𝟙-uniq _

module _ {ℓ} where
    𝟙ˡ : Lookup {ℓ} 𝟙ᵉ
    𝟙ˡ = const

    𝟙ᶠ : Focus {ℓ} 𝟙ᵉ
    𝟙ᶠ = proj₂

    open Explorableₛ  {ℓ} 𝟙ⁱ public using () renaming (reify   to 𝟙ʳ)
    open Explorableₛₛ {ℓ} 𝟙ⁱ public using () renaming (unfocus to 𝟙ᵘ)

explore𝟙          = 𝟙ᵉ
explore𝟙-ind      = 𝟙ⁱ
lookup𝟙           = 𝟙ˡ
reify𝟙            = 𝟙ʳ
focus𝟙            = 𝟙ᶠ
unfocus𝟙          = 𝟙ᵘ
sum𝟙              = 𝟙ˢ
adequate-sum𝟙     = 𝟙ˢ-ok
product𝟙          = 𝟙ᵖ
adequate-product𝟙 = 𝟙ᵖ-ok

-- DEPRECATED
module _ {{_ : UA}} where
  open ExplorableRecord
  μ𝟙 : Explorable 𝟙
  μ𝟙 = mk _ 𝟙ⁱ 𝟙ˢ-ok
