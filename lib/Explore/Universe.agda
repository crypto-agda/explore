open import Level.NP
open import Type
open import Data.One
open import Data.Two
open import Data.Product
open import Data.Sum
open import Explore.Type
open import Explore.One
open import Explore.Two
open import Explore.Product
open import Explore.Sum

module Explore.Universe where

open Operators

infixr 2 _×′_

data Ty : ★
El : Ty → ★

data Ty where
  𝟙′ 𝟚′ : Ty
  _×′_ _⊎′_ : Ty → Ty → Ty
  Σ′ : (t : Ty) → (El t → Ty) → Ty

El 𝟙′ = 𝟙
El 𝟚′ = 𝟚
El (s ×′ t) = El s × El t
El (s ⊎′ t) = El s ⊎ El t
El (Σ′ t f) = Σ (El t) λ x → El (f x)
--El (t ^′ x) = {!Vec (El t) x!}

module _ {ℓ} where

    exploreU : ∀ t → Explore ℓ (El t)
    exploreU 𝟙′ = 𝟙ᵉ
    exploreU 𝟚′ = 𝟚ᵉ
    exploreU (s ×′ t) = exploreU s ×ᵉ exploreU t
    exploreU (s ⊎′ t) = exploreU s ⊎ᵉ exploreU t
    exploreU (Σ′ t f)  = exploreΣ (exploreU t) λ {x} → exploreU (f x)
    --exploreU (t ^′ x) = {!!}

    exploreU-ind : ∀ t → ExploreInd ℓ (exploreU t)
    exploreU-ind 𝟙′ = 𝟙ⁱ
    exploreU-ind 𝟚′ = 𝟚ⁱ
    exploreU-ind (s ×′ t) = exploreU-ind s ×ⁱ exploreU-ind t
    exploreU-ind (s ⊎′ t) = exploreU-ind s ⊎ⁱ exploreU-ind t
    exploreU-ind (Σ′ t f) = exploreΣ-ind (exploreU-ind t) λ {x} → exploreU-ind (f x)
    --exploreU-ind (t ^′ x) = {!!}

module _ {ℓ} where
    lookupU : ∀ t → Lookup {ℓ} (exploreU t)
    lookupU 𝟙′ = 𝟙ˡ
    lookupU 𝟚′ = 𝟚ˡ
    lookupU (s ×′ t) = lookup× {_} {_} {_} {exploreU s} {exploreU t} (lookupU s) (lookupU t)
    lookupU (s ⊎′ t) = lookup⊎ {_} {_} {_} {exploreU s} {exploreU t} (lookupU s) (lookupU t)
    lookupU (Σ′ t f) = lookupΣ {_} {_} {_} {exploreU t} {λ {x} → exploreU (f x)} (lookupU t) (λ {x} → lookupU (f x))
    --lookupU (t ^′ x) = {!!}
-- -}
