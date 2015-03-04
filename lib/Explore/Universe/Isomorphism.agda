{-# OPTIONS --without-K #-}
open import Type
open import Function.Extensionality using (FunExt)

open import HoTT using (UA; module Equivalences)
open Equivalences

open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
open import Explore.Universe.Base

-- See Explore.Fin for an example of the use of this module
module Explore.Universe.Isomorphism {A : ★₀} u (e : El u ≃ A) where

open import Explore.Isomorphism e

module _ {ℓ} where
  isoᵉ : Explore ℓ A
  isoᵉ = explore-iso (explore u)

  module _ {p} where
    isoⁱ : ExploreInd p isoᵉ
    isoⁱ = explore-iso-ind (exploreU-ind u)

module _ {ℓ} where
  isoˡ : Lookup {ℓ} isoᵉ
  isoˡ = lookup-iso {ℓ} {explore u} (lookupU u)

  isoᶠ : Focus {ℓ} isoᵉ
  isoᶠ = focus-iso {ℓ} {explore u} (focusU u)

  isoʳ : Reify {ℓ} isoᵉ
  isoʳ = FromExploreInd-iso.reify (exploreU-ind u)

  isoᵘ : Unfocus {ℓ} isoᵉ
  isoᵘ = FromExploreInd-iso.unfocus (exploreU-ind u)

isoˢ : Sum A
isoˢ = sum-iso (sum u)

isoᵖ : Product A
isoᵖ = product-iso (sum u)

module _ {{_ : UA}}{{_ : FunExt}} where
  isoˢ-ok : Adequate-sum isoˢ
  isoˢ-ok = sum-iso-ok (adequate-sumU u)

  open Adequate-sum₀ isoˢ-ok isoˢ-ok public renaming (sumStableUnder to isoˢ-stableUnder)
