open import Type
open import Level.NP
open import Explore.Type
open import Explore.Explorable
open import Data.One
open import Function.NP
open import Data.Product
import Function.Inverse.NP as FI
open import Relation.Binary.PropositionalEquality using (refl)
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP
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

module _ {ℓ} where
    𝟙ˡ : Lookup {ℓ} 𝟙ᵉ
    𝟙ˡ = const

    𝟙ᶠ : Focus {ℓ} 𝟙ᵉ
    𝟙ᶠ = proj₂

open Explorable₀  𝟙ⁱ public using () renaming (sum     to 𝟙ˢ; product to 𝟙ᵖ)
open Explorable₁₀ 𝟙ⁱ public using () renaming (reify   to 𝟙ʳ)
open Explorable₁₁ 𝟙ⁱ public using () renaming (unfocus to 𝟙ᵘ)

𝟙ˢ-ok : AdequateSum 𝟙ˢ
𝟙ˢ-ok _ = FI.sym 𝟙×A↔A

𝟙ᵖ-ok : AdequateProduct 𝟙ᵖ
𝟙ᵖ-ok f = FI.sym Π𝟙F↔F

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
μ𝟙 : Explorable 𝟙
μ𝟙 = mk _ 𝟙ⁱ 𝟙ˢ-ok
