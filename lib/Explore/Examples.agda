module Explore.Examples where

open import Type
open import Level.NP
open import Data.Maybe.NP
open import Data.List
open import Data.Two

open import Explore.Core
open import Explore.Explorable
open import Explore.Monad ₀ renaming (map to map-explore)

module E where
  open FromExplore₀ public
  open FromExplore public

module M {Msg Digest : ★}
         (_==_ : Digest → Digest → 𝟚)
         (H : Msg → Digest)
         (exploreMsg : Explore ₀ Msg)
         (d : Digest) where

  module V1 where
    list-H⁻¹ : List Msg
    list-H⁻¹ = exploreMsg [] _++_ (λ m → [0: [] 1: [ m ] ] (H m == d))

  module ExploreMsg = FromExplore₀ exploreMsg

  module V2 where
    first-H⁻¹ : Maybe Msg
    first-H⁻¹ = ExploreMsg.findKey (λ m → H m == d)

  module V3 where
    explore-H⁻¹ : Explore ₀ Msg
    explore-H⁻¹ ε _⊕_ f = exploreMsg ε _⊕_ (λ m → [0: ε 1: f m ] (H m == d))

  module V4 where
    explore-H⁻¹ : Explore ₀ Msg
    explore-H⁻¹ = exploreMsg >>= λ m → [0: empty-explore 1: point-explore m ] (H m == d)

  module V5 where

    explore-H⁻¹ : Explore ₀ Msg
    explore-H⁻¹ = filter-explore (λ m → H m == d) exploreMsg

    list-H⁻¹ : List Msg
    list-H⁻¹ = E.list explore-H⁻¹

    first-H⁻¹ : Maybe Msg
    first-H⁻¹ = E.first explore-H⁻¹

  module V6 where
    explore-H⁻¹ : Explore ₀ Msg
    explore-H⁻¹ = explore-endo (filter-explore (λ m → H m == d) exploreMsg)

    list-H⁻¹ : List Msg
    list-H⁻¹ = E.list explore-H⁻¹

    first-H⁻¹ : Maybe Msg
    first-H⁻¹ = E.first explore-H⁻¹

    last-H⁻¹ : Maybe Msg
    last-H⁻¹ = E.last explore-H⁻¹

open import Data.Two
open import Data.Product
open import Explore.Two
open import Explore.Product
open Explore.Product.Operators
open import Relation.Binary.PropositionalEquality
Msg = 𝟚 × 𝟚
Digest = 𝟚
-- _==_ : Digest → Digest → 𝟚
H : Msg → Digest
H (x , y) = x xor y
Msgᵉ : Explore ₀ Msg
Msgᵉ = 𝟚ᵉ ×ᵉ 𝟚ᵉ
module N5 = M.V5 _==_ H Msgᵉ
module N6 = M.V6 _==_ H Msgᵉ
test5 = N5.list-H⁻¹
test6-list : N6.list-H⁻¹ 0₂ ≡ 0₂ , 0₂ ∷ 1₂ , 1₂ ∷ []
test6-list = refl
test6-rev-list : E.list (E.backward (N6.explore-H⁻¹ 0₂)) ≡ 1₂ , 1₂ ∷ 0₂ , 0₂ ∷ []
test6-rev-list = refl
test6-first : N6.first-H⁻¹ 0₂ ≡ just (0₂ , 0₂)
test6-first = refl
test6-last : N6.last-H⁻¹ 0₂ ≡ just (1₂ , 1₂)
test6-last = refl
