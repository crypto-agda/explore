{-# OPTIONS --without-K #-}
open import Level.NP
open import Type hiding (★)
open import Type.Identities
open import Function.NP
open import Function.Extensionality
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Binary.NP
open import HoTT
open Equivalences

open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
import Explore.Monad

-- NOTE: it would be nice to have another module to change the definition of an exploration
-- function by an extensionally equivalent one. Combined with this module one could both
-- pick the reduction behavior we want and save some proof effort.
module Explore.Isomorphism
  {A B : ★₀} (e : A ≃ B) where

private
  module M {ℓ} = Explore.Monad ℓ
  e⁻ = ≃-sym e
  f = –> e
  g = <– e

module _ {ℓ} (Aᵉ : Explore ℓ A) where
  explore-iso : Explore ℓ B
  explore-iso = M.map f Aᵉ

private
  Bᵉ = explore-iso

module _ {ℓ p} {Aᵉ : Explore ℓ A} (Aⁱ : ExploreInd p Aᵉ) where
  explore-iso-ind : ExploreInd p (Bᵉ Aᵉ)
  explore-iso-ind = M.map-ind f Aⁱ

private
  Bⁱ = explore-iso-ind

{-
module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aˡ : Lookup {ℓ} Aᵉ) where
  lookup-iso : Lookup {ℓ} (Bᵉ Aᵉ)
  lookup-iso {C} d b = tr C {!e!} (Aˡ d (g b))

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aᶠ : Focus {ℓ} Aᵉ) where
  focus-iso : Focus {ℓ} (Bᵉ Aᵉ)
  focus-iso {C} (b , c) = Aᶠ (g b , c')
    where c' = {!tr C (! (–>-inv-r e b)) c!}
-}

module _ (Aˢ : Sum A) where
  sum-iso : Sum B
  sum-iso h = Aˢ (h ∘ f)

module _ (Aᵖ : Product A) where
  product-iso : Product B
  product-iso h = Aᵖ (h ∘ f)

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aⁱ : ExploreInd ℓ Aᵉ) where
  open Explorableₛ (Bⁱ Aⁱ) public using () renaming (reify   to reify-iso)

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aⁱ : ExploreInd (ₛ ℓ) Aᵉ) where
  open Explorableₛₛ (Bⁱ Aⁱ) public using () renaming (unfocus to unfocus-iso)

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (ΣAᵉ-ok : Adequate-Σᵉ Aᵉ) {{_ : UA}} {{_ : FunExt}} where
  Σ-iso-ok : Adequate-Σᵉ (Bᵉ Aᵉ)
  Σ-iso-ok F = ΣAᵉ-ok (F ∘ f) ∙ Σ-fst≃ e _

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (ΠAᵉ-ok : Adequate-Πᵉ Aᵉ) {{_ : UA}} {{_ : FunExt}} where
  Π-iso-ok : Adequate-Πᵉ (Bᵉ Aᵉ)
  Π-iso-ok F = ΠAᵉ-ok (F ∘ f) ∙ Π-dom≃ e _

module _ {Aˢ : Sum A} (Aˢ-ok : Adequate-sum Aˢ) {{_ : UA}} {{_ : FunExt}} where
  sum-iso-ok : Adequate-sum (sum-iso Aˢ)
  sum-iso-ok h = Aˢ-ok (h ∘ f) ∙ Σ-fst≃ e _

module _ {Aᵖ : Product A} (Aᵖ-ok : Adequate-product Aᵖ) {{_ : UA}} {{_ : FunExt}} where
  product-iso-ok : Adequate-product (product-iso Aᵖ)
  product-iso-ok g = Aᵖ-ok (g ∘ f) ∙ Π-dom≃ e _

-- -}
-- -}
-- -}
