open import Level.NP
open import Type
open import Data.One
open import Data.Two
open import Data.Product
open import Explore.Type
open import Explore.One
open import Explore.Two
open import Explore.Product

module Explore.Universe where

open Operators

{-
open import FunUniverse.Data
-}
data Ty : ★ where
  𝟙′ 𝟚′ : Ty
  _×′_  : Ty → Ty → Ty

El : Ty → ★
El 𝟙′ = 𝟙
El 𝟚′ = 𝟚
El (u₀ ×′ u₁) = El u₀ × El u₁
--El (u ^′ x) = {!Vec (El u) x!}

module _ {ℓ} where

    exploreU : ∀ u → Explore ℓ (El u)
    exploreU 𝟙′ = 𝟙ᵉ
    exploreU 𝟚′ = 𝟚ᵉ
    exploreU (u ×′ u₁) = exploreU u ×ᵉ exploreU u₁
    --exploreU (u ^′ x) = {!!}

    exploreU-ind : ∀ u → ExploreInd ℓ (exploreU u)
    exploreU-ind 𝟙′ = 𝟙ⁱ
    exploreU-ind 𝟚′ = 𝟚ⁱ
    exploreU-ind (u ×′ u₁) = exploreU-ind u ×ⁱ exploreU-ind u₁
    --exploreU-ind (u ^′ x) = {!!}

module _ {ℓ} where
    lookupU : ∀ u → Lookup {ℓ} (exploreU {ₛ ℓ} u)
    lookupU 𝟙′ = 𝟙ˡ
    lookupU 𝟚′ = 𝟚ˡ
    lookupU (u ×′ u₁) = lookup× {_} {_} {_} {exploreU u} {exploreU u₁} (lookupU u) (lookupU u₁)
    --lookupU (u ^′ x) = {!!}
