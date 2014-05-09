open import Type
open import Type.Identities
open import Level.NP
open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
open import Data.Zero
open import Function.NP
open import Function.Extensionality
open import Data.Product
open import Relation.Binary.PropositionalEquality.NP using (_≡_; refl; _∙_; !_)
open import HoTT
open Equivalences

import Explore.Monad
open import Explore.Isomorphism

module Explore.Zero where


module _ {ℓ} where
    𝟘ᵉ : Explore ℓ 𝟘
    𝟘ᵉ = empty-explore
    {- or
    𝟘ᵉ ε _ _ = ε
    -}

    𝟘ⁱ : ∀ {p} → ExploreInd p 𝟘ᵉ
    𝟘ⁱ = empty-explore-ind
    {- or
    𝟘ⁱ _ Pε _ _ = Pε
    -}

module _ {ℓ₁ ℓ₂ ℓᵣ} {R : 𝟘 → 𝟘 → ★₀} where
    ⟦𝟘ᵉ⟧ : ⟦Explore⟧ᵤ ℓ₁ ℓ₂ ℓᵣ R 𝟘ᵉ 𝟘ᵉ
    ⟦𝟘ᵉ⟧ _ εᵣ _ _ = εᵣ

open Explorable₀  𝟘ⁱ public using () renaming (sum     to 𝟘ˢ; product to 𝟘ᵖ)

module _ {ℓ} where
    open Explorableₛ  {ℓ} 𝟘ⁱ public using () renaming (reify    to 𝟘ʳ)
    open Explorableₛₛ {ℓ} 𝟘ⁱ public using () renaming (unfocus  to 𝟘ᵘ)

    𝟘ˡ : Lookup {ℓ} 𝟘ᵉ
    𝟘ˡ _ ()

    𝟘ᶠ : Focus {ℓ} 𝟘ᵉ
    𝟘ᶠ ((), _)

    module _ {{_ : UA}} where
        Σᵉ𝟘-ok : Adequate-Σᵉ {ℓ} 𝟘ᵉ
        Σᵉ𝟘-ok _ = ! Σ𝟘-lift∘fst

    module _ {{_ : UA}}{{_ : FunExt}} where
        Πᵉ𝟘-ok : Adequate-Πᵉ {ℓ} 𝟘ᵉ
        Πᵉ𝟘-ok _ = ! Π𝟘-uniq _

module _ {{_ : UA}} where
    𝟘ˢ-ok : Adequate-sum 𝟘ˢ
    𝟘ˢ-ok _ = Fin0≡𝟘 ∙ ! Σ𝟘-fst

module _ {{_ : UA}}{{_ : FunExt}} where
    𝟘ᵖ-ok : Adequate-product 𝟘ᵖ
    𝟘ᵖ-ok _ = Fin1≡𝟙 ∙ ! (Π𝟘-uniq₀ _)

explore𝟘          = 𝟘ᵉ
explore𝟘-ind      = 𝟘ⁱ
lookup𝟘           = 𝟘ˡ
reify𝟘            = 𝟘ʳ
focus𝟘            = 𝟘ᶠ
unfocus𝟘          = 𝟘ᵘ
sum𝟘              = 𝟘ˢ
adequate-sum𝟘     = 𝟘ˢ-ok
product𝟘          = 𝟘ᵖ
adequate-product𝟘 = 𝟘ᵖ-ok


Lift𝟘ᵉ : ∀ {m} → Explore m (Lift 𝟘)
Lift𝟘ᵉ = explore-iso (≃-sym Lift≃id) 𝟘ᵉ

ΣᵉLift𝟘-ok : ∀ {{_ : UA}}{{_ : FunExt}}{m} → Adequate-Σᵉ {m} Lift𝟘ᵉ
ΣᵉLift𝟘-ok = Σ-iso-ok (≃-sym Lift≃id) {Aᵉ = 𝟘ᵉ} Σᵉ𝟘-ok

-- DEPRECATED
module _ {{_ : UA}} where
    open ExplorableRecord
    μ𝟘 : Explorable 𝟘
    μ𝟘 = mk _ 𝟘ⁱ 𝟘ˢ-ok
-- -}
