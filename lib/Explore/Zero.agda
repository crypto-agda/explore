open import Type
open import Level.NP
open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
open import Data.Zero
open import Function.NP
open import Data.Product
import Function.Inverse.NP as FI
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP
import Explore.Monad

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

open Explorable₀  𝟘ⁱ public using () renaming (sum     to 𝟘ˢ; product to 𝟘ᵖ)

module _ {ℓ} where
    open Explorableₛ  {ℓ} 𝟘ⁱ public using () renaming (reify    to 𝟘ʳ)
    open Explorableₛₛ {ℓ} 𝟘ⁱ public using () renaming (unfocus  to 𝟘ᵘ)

    𝟘ˡ : Lookup {ℓ} 𝟘ᵉ
    𝟘ˡ _ ()

    𝟘ᶠ : Focus {ℓ} 𝟘ᵉ
    𝟘ᶠ ((), _)


𝟘ˢ-ok : AdequateSum 𝟘ˢ
𝟘ˢ-ok _ = FI.sym (Σ𝟘↔𝟘 _) FI.∘ Fin0↔𝟘

𝟘ᵖ-ok : (ext𝟘 : ∀ {F} (f g : Π 𝟘 F) → f ≡ g) → AdequateProduct 𝟘ᵖ
𝟘ᵖ-ok ext𝟘 _ = FI.sym (Π𝟘↔𝟙 ext𝟘) FI.∘ Fin1↔𝟙

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

-- DEPRECATED
μ𝟘 : Explorable 𝟘
μ𝟘 = mk _ 𝟘ⁱ 𝟘ˢ-ok
-- -}
