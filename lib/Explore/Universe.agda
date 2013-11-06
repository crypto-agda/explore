open import Level.NP
open import Type
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Function.Inverse.NP using (_↔_)
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as Inv
open Inv using (_↔_)

open import Explore.Core
open import Explore.Properties
open import Explore.Zero
open import Explore.One
open import Explore.Two
open import Explore.Product
open import Explore.Sum
open import Explore.Explorable
import Explore.Isomorphism

module Explore.Universe where

open Operators

infixr 2 _×′_
infix  8 _^′_

data U : ★
El : U → ★

data U where
  𝟘′ 𝟙′ 𝟚′ : U
  _×′_ _⊎′_ : U → U → U
  Σ′ : (t : U) → (El t → U) → U

El 𝟘′ = 𝟘
El 𝟙′ = 𝟙
El 𝟚′ = 𝟚
El (s ×′ t) = El s × El t
El (s ⊎′ t) = El s ⊎ El t
El (Σ′ t f) = Σ (El t) λ x → El (f x)

_^′_ : U → ℕ → U
t ^′ zero  = t
t ^′ suc n = t ×′ t ^′ n

module _ {ℓ} where

    exploreU : ∀ t → Explore ℓ (El t)
    exploreU 𝟘′ = 𝟘ᵉ
    exploreU 𝟙′ = 𝟙ᵉ
    exploreU 𝟚′ = 𝟚ᵉ
    exploreU (s ×′ t) = exploreU s ×ᵉ exploreU t
    exploreU (s ⊎′ t) = exploreU s ⊎ᵉ exploreU t
    exploreU (Σ′ t f) = exploreΣ (exploreU t) λ {x} → exploreU (f x)

    exploreU-ind : ∀ {p} t → ExploreInd p (exploreU t)
    exploreU-ind 𝟘′ = 𝟘ⁱ
    exploreU-ind 𝟙′ = 𝟙ⁱ
    exploreU-ind 𝟚′ = 𝟚ⁱ
    exploreU-ind (s ×′ t) = exploreU-ind s ×ⁱ exploreU-ind t
    exploreU-ind (s ⊎′ t) = exploreU-ind s ⊎ⁱ exploreU-ind t
    exploreU-ind (Σ′ t f) = exploreΣ-ind (exploreU-ind t) λ {x} → exploreU-ind (f x)

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
adequate-sumU 𝟘′       = 𝟘ˢ-ok
adequate-sumU 𝟙′       = 𝟙ˢ-ok
adequate-sumU 𝟚′       = 𝟚ˢ-ok
adequate-sumU (s ×′ t) = adequate-sumΣ (adequate-sumU s) (adequate-sumU t)
adequate-sumU (s ⊎′ t) = adequate-sum⊎ (adequate-sumU s) (adequate-sumU t)
adequate-sumU (Σ′ t f) = adequate-sumΣ (adequate-sumU t) (λ {x} → adequate-sumU (f x))

module _ {ℓ} where
    lookupU : ∀ t → Lookup {ℓ} (exploreU t)
    lookupU 𝟘′ = 𝟘ˡ
    lookupU 𝟙′ = 𝟙ˡ
    lookupU 𝟚′ = 𝟚ˡ
    lookupU (s ×′ t) = lookup× {_} {_} {_} {exploreU s} {exploreU t} (lookupU s) (lookupU t)
    lookupU (s ⊎′ t) = lookup⊎ {_} {_} {_} {exploreU s} {exploreU t} (lookupU s) (lookupU t)
    lookupU (Σ′ t f) = lookupΣ {_} {_} {_} {exploreU t} {λ {x} → exploreU (f x)} (lookupU t) (λ {x} → lookupU (f x))

    focusU : ∀ t → Focus {ℓ} (exploreU t)
    focusU 𝟘′ = 𝟘ᶠ
    focusU 𝟙′ = 𝟙ᶠ
    focusU 𝟚′ = 𝟚ᶠ
    focusU (s ×′ t) = focus× {_} {_} {_} {exploreU s} {exploreU t} (focusU s) (focusU t)
    focusU (s ⊎′ t) = focus⊎ {_} {_} {_} {exploreU s} {exploreU t} (focusU s) (focusU t)
    focusU (Σ′ t f) = focusΣ {_} {_} {_} {exploreU t} {λ {x} → exploreU (f x)} (focusU t) (λ {x} → focusU (f x))

-- See Explore.Fin for an example of the use of this module
module Isomorphism {A : ★₀} u (u↔A : El u ↔ A) where
  open Explore.Isomorphism u↔A

  module _ {ℓ} where
    isoᵉ : Explore ℓ A
    isoᵉ = explore-iso (exploreU u)

    module _ {p} where
      isoⁱ : ExploreInd p isoᵉ
      isoⁱ = explore-iso-ind (exploreU-ind u)

  module _ {ℓ} where
    isoˡ : Lookup {ℓ} isoᵉ
    isoˡ = lookup-iso {ℓ} {exploreU u} (lookupU u)

    isoᶠ : Focus {ℓ} isoᵉ
    isoᶠ = focus-iso {ℓ} {exploreU u} (focusU u)

  isoˢ : Sum A
  isoˢ = sum-iso (sumU u)

  isoᵖ : Product A
  isoᵖ = product-iso (sumU u)

  isoʳ : Reify isoᵉ
  isoʳ = reify-iso (exploreU-ind u)

  isoᵘ : Unfocus isoᵉ
  isoᵘ = unfocus-iso (exploreU-ind u)

  isoˢ-ok : AdequateSum isoˢ
  isoˢ-ok = sum-iso-ok (adequate-sumU u)

  -- SUI
  open AdequateSum₀ isoˢ-ok isoˢ-ok public renaming (sumStableUnder to isoˢ-stableUnder)

  μiso : Explorable A
  μiso = mk _ isoⁱ isoˢ-ok

FinU : ℕ → U
FinU zero    = 𝟘′
FinU (suc n) = 𝟙′ ⊎′ FinU n

FinU↔Fin : ∀ n → El (FinU n) ↔ Fin n
FinU↔Fin zero    = Inv.sym Fin0↔𝟘
FinU↔Fin (suc n) = Inv.sym Fin∘suc↔𝟙⊎Fin Inv.∘ Inv.id ⊎-cong FinU↔Fin n

-- -}
