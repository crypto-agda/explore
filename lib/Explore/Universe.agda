open import Level.NP
open import Type
open import Data.One
open import Data.Two
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin using (Fin)
open import Explore.Type
open import Explore.One
open import Explore.Two
open import Explore.Product
open import Explore.Sum
open import Explore.Fin
open import Explore.Explorable

module Explore.Universe where

open Operators

infixr 2 _×′_
infix  8 _^′_

data U : ★
El : U → ★

data U where
  𝟙′ 𝟚′ : U
  _×′_ _⊎′_ : U → U → U
  Σ′ : (t : U) → (El t → U) → U
--FinS′ : ℕ → U

El 𝟙′ = 𝟙
El 𝟚′ = 𝟚
El (s ×′ t) = El s × El t
El (s ⊎′ t) = El s ⊎ El t
El (Σ′ t f) = Σ (El t) λ x → El (f x)
--El (FinS′ n) = FinS n

_^′_ : U → ℕ → U
t ^′ zero  = t
t ^′ suc n = t ×′ t ^′ n

module _ {ℓ} where

    exploreU : ∀ t → Explore ℓ (El t)
    exploreU 𝟙′ = 𝟙ᵉ
    exploreU 𝟚′ = 𝟚ᵉ
    exploreU (s ×′ t) = exploreU s ×ᵉ exploreU t
    exploreU (s ⊎′ t) = exploreU s ⊎ᵉ exploreU t
    exploreU (Σ′ t f) = exploreΣ (exploreU t) λ {x} → exploreU (f x)
  --exploreU (FinS′ n) = FinSᵉ n

    exploreU-ind : ∀ {p} t → ExploreInd p (exploreU t)
    exploreU-ind 𝟙′ = 𝟙ⁱ
    exploreU-ind 𝟚′ = 𝟚ⁱ
    exploreU-ind (s ×′ t) = exploreU-ind s ×ⁱ exploreU-ind t
    exploreU-ind (s ⊎′ t) = exploreU-ind s ⊎ⁱ exploreU-ind t
    exploreU-ind (Σ′ t f) = exploreΣ-ind (exploreU-ind t) λ {x} → exploreU-ind (f x)
  --exploreU-ind (FinS′ n) = FinSⁱ n

module _ (t : U) where
  private
    tᵉ : ∀ {ℓ} → Explore ℓ (El t)
    tᵉ = exploreU t
    tⁱ : ∀ {ℓ p} → ExploreInd p {ℓ} tᵉ
    tⁱ = exploreU-ind t
  open Explorable₀  tⁱ public using () renaming (sum     to sumU; product to productU)
  open Explorable₁₀ tⁱ public using () renaming (reify   to reifyU)
  open Explorable₁₁ tⁱ public using () renaming (unfocus to unfocusU)

adequate-sumU : ∀ t → AdequateSum (sumU t)
adequate-sumU 𝟙′       = 𝟙ˢ-ok
adequate-sumU 𝟚′       = 𝟚ˢ-ok
adequate-sumU (s ×′ t) = adequate-sumΣ (adequate-sumU s) (adequate-sumU t)
adequate-sumU (s ⊎′ t) = adequate-sum⊎ (adequate-sumU s) (adequate-sumU t)
adequate-sumU (Σ′ t f) = adequate-sumΣ (adequate-sumU t) (λ {x} → adequate-sumU (f x))
--adequate-sumU (FinS′ n) = {!!}

module _ {ℓ} where
    lookupU : ∀ t → Lookup {ℓ} (exploreU t)
    lookupU 𝟙′ = 𝟙ˡ
    lookupU 𝟚′ = 𝟚ˡ
    lookupU (s ×′ t) = lookup× {_} {_} {_} {exploreU s} {exploreU t} (lookupU s) (lookupU t)
    lookupU (s ⊎′ t) = lookup⊎ {_} {_} {_} {exploreU s} {exploreU t} (lookupU s) (lookupU t)
    lookupU (Σ′ t f) = lookupΣ {_} {_} {_} {exploreU t} {λ {x} → exploreU (f x)} (lookupU t) (λ {x} → lookupU (f x))
  --lookupU (FinS′ n) = FinSˡ n

    focusU : ∀ t → Focus {ℓ} (exploreU t)
    focusU 𝟙′ = 𝟙ᶠ
    focusU 𝟚′ = 𝟚ᶠ
    focusU (s ×′ t) = focus× {_} {_} {_} {exploreU s} {exploreU t} (focusU s) (focusU t)
    focusU (s ⊎′ t) = focus⊎ {_} {_} {_} {exploreU s} {exploreU t} (focusU s) (focusU t)
    focusU (Σ′ t f) = focusΣ {_} {_} {_} {exploreU t} {λ {x} → exploreU (f x)} (focusU t) (λ {x} → focusU (f x))
  --focusU (FinS′ n) = FinSᶠ n
-- -}
