{-# OPTIONS --without-K #-}
open import Level.NP
open import Type hiding (★)
open import Function.NP
open import Data.Product
open import Data.Sum
import Relation.Binary.PropositionalEquality as ≡
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as Inv
open Inv using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Relation.Binary.NP

open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
import Explore.Monad

-- NOTE: it would be nice to have another module to change the definition of an exploration
-- function by an extensionally equivalent one. Combined with this module one could both
-- pick the reduction behavior we want and save some proof effort.
module Explore.Isomorphism
  {A B : ★₀} (A↔B : A ↔ B) where

private
  module M {ℓ} = Explore.Monad ℓ

module _ {ℓ} (Aᵉ : Explore ℓ A) where
  explore-iso : Explore ℓ B
  explore-iso = M.map (to A↔B) Aᵉ

private
  Bᵉ = explore-iso

module _ {ℓ p} {Aᵉ : Explore ℓ A} (Aⁱ : ExploreInd p Aᵉ) where
  explore-iso-ind : ExploreInd p (Bᵉ Aᵉ)
  explore-iso-ind = M.map-ind (to A↔B) Aⁱ

private
  Bⁱ = explore-iso-ind

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aˡ : Lookup {ℓ} Aᵉ) where
  lookup-iso : Lookup {ℓ} (Bᵉ Aᵉ)
  lookup-iso {C} d b
    = ≡.subst C (Inverse.right-inverse-of A↔B b)
                (Aˡ d (from A↔B b))

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aᶠ : Focus {ℓ} Aᵉ) where
  focus-iso : Focus {ℓ} (Bᵉ Aᵉ)
  focus-iso {C} (b , c) = Aᶠ (from A↔B b , c')
    where c' = ≡.subst C (≡.sym (Inverse.right-inverse-of A↔B b)) c

module _ (Aˢ : Sum A) where
  sum-iso : Sum B
  sum-iso f = Aˢ (f ∘ to A↔B)

module _ (Aᵖ : Product A) where
  product-iso : Product B
  product-iso f = Aᵖ (f ∘ to A↔B)

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aⁱ : ExploreInd ℓ Aᵉ) where
  open Explorableₛ (Bⁱ Aⁱ) public using () renaming (reify   to reify-iso)

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aⁱ : ExploreInd (ₛ ℓ) Aᵉ) where
  open Explorableₛₛ (Bⁱ Aⁱ) public using () renaming (unfocus to unfocus-iso)

module _ {Aˢ : Sum A} (Aˢ-ok : AdequateSum Aˢ) where
  sum-iso-ok : AdequateSum (sum-iso Aˢ)
  sum-iso-ok f = sym-first-iso A↔B Inv.∘ Aˢ-ok (f ∘ to A↔B)

{- requires extensional equality
module _ {Aᵖ : Product A} (Aᵖ-ok : AdequateProduct Aᵖ) where
  product-iso-ok : AdequateProduct (product-iso Aᵖ)
  product-iso-ok f = arg-iso A↔B Inv.∘ Aᵖ-ok (f ∘ to A↔B)
-}

  {-
module _ (Aᵉ : Explore₁ A) where
  focused-iso : Focused {₀} (Bᵉ Aᵉ)
  focused-iso = inverses {!!} {!!} {!(⇒)!} {!(⇐)!}
    where ⇒ : (x : Σ _ _) → _
          ⇒ (b , c) = {!!}
          ⇐ : (x : _ ⊎ _) → _
          ⇐ (inj₁ x) = {!!}
          ⇐ (inj₂ x) = {!!}
-}
