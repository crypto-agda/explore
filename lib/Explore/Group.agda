{-# OPTIONS --without-K #-}
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import HoTT
open import Function.Extensionality
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Algebra.Group.Isomorphism
open import Function using (id; _∘_ ; flip)
open import Relation.Binary.PropositionalEquality.NP

open import Explore.Core
open import Explore.Properties
import Explore.Explorable as E

open Equivalences

module Explore.Group where

module FromGroupHomomorphism
  {ℓ}{A B : Set ℓ}(𝔾+ : Group A)(𝔾* : Group B)
  (φ : A → B)(φ-hom : GroupHomomorphism 𝔾+ 𝔾* φ)
  where

 open Additive-Group 𝔾+
 open Multiplicative-Group 𝔾*

 module LiftGroupHomomorphism
  {i}{I : Set i}
  {explore : ∀ {ℓ} → Explore ℓ I}
  (explore-ind : ∀ {p ℓ} → ExploreInd {ℓ} p explore)
  (g : I → A)
  where
  open GroupHomomorphism φ-hom

  Σᴵ = explore 0# _+_
  Πᴵ = explore 1# _*_

  lift-hom : φ (Σᴵ g) ≡ Πᴵ (φ ∘ g)
  lift-hom = E.FromExploreInd.LiftHom.lift-hom explore-ind _≡_ refl trans 0# _+_ 1# _*_ *= φ g 0-hom-1 hom

 module FromExplore
   {ℓx} {X : Set ℓx}(z : X)(_⊕_ : X → X → X)
   (exploreᴬ  : Explore ℓx A)
   (exploreᴬ= : ExploreExt exploreᴬ)
   (let [⊕] = exploreᴬ z _⊕_)
   (O : B → X)
   (sui : ∀ {k} → [⊕] (O ∘ φ) ≡ [⊕] (O ∘ _*_ k ∘ φ))
   where

    +-stable : ∀ {k} → [⊕] (O ∘ φ) ≡ [⊕] (O ∘ φ ∘ _+_ k)
    +-stable = Algebra.Group.Homomorphism.Stability.+-stable 𝔾+ 𝔾* φ φ-hom
                  ([⊕] ∘ _∘_ O) (exploreᴬ= _ _ ∘ _∘_ (ap O)) sui

module FromGroupIsomorphism
         {ℓa}{ℓb}{A : Set ℓa}{B : Set ℓb}(𝔾+ : Group A)(𝔾* : Group B)
         (φ : A → B)(φ-iso : GroupIsomorphism 𝔾+ 𝔾* φ) where
 open GroupIsomorphism φ-iso

 open Additive-Group 𝔾+
 open Multiplicative-Group 𝔾*

 module FromBigOp
  {ℓx}{X : Set ℓx}(F : BigOp X A)
  (F= : ∀ {g₀ g₁ : A → X} → g₀ ≗ g₁ → F g₀ ≡ F g₁)
  (O : B → X)
  (sui : ∀ {k} → F (O ∘ φ) ≡ F (O ∘ φ ∘ _+_ k))
  where

  _≈_ : (g₀ g₁ : B → B) → Set ℓx
  g₀ ≈ g₁ = F (O ∘ g₀ ∘ φ) ≡ F (O ∘ g₁ ∘ φ)

  -- The core of the proof is there:
  open Algebra.Group.Isomorphism.Stability 𝔾+ 𝔾* φ φ-iso

  id≈k* : ∀ {k} → id ≈ _*_ k
  id≈k* = *-stable (F  ∘ _∘_ O)
                   (F= ∘ _∘_ (ap O))
                   sui

  k₀*≈k₁* : ∀ {k₀ k₁} → _*_ k₀ ≈ _*_ k₁
  k₀*≈k₁* = ! id≈k* ∙ id≈k*

 module FromExplore
  {ℓx}{X : Set ℓx}(z : X)(_⊕_ : X → X → X)
  (exploreᴬ  : Explore ℓx A)
  (exploreᴬ= : ExploreExt exploreᴬ)
  = FromBigOp (exploreᴬ z _⊕_) (exploreᴬ= z _⊕_)

module FromAdequate-sum
  {ℓb}{A : Set}{B : Set ℓb}(𝔾+ : Group A)(𝔾* : Group B)
  (φ : A → B)(φ-iso : GroupIsomorphism 𝔾+ 𝔾* φ)
  {sum : Sum A}
  (open Adequacy _≡_)
  (sum-adq : Adequate-sum sum)
  {{_ : UA}}{{_ : FunExt}}
  (open E.FromAdequate-sum sum-adq)
  (O : B → ℕ)
  (open Additive-Group 𝔾+)
  (open FromGroupIsomorphism 𝔾+ 𝔾* φ φ-iso)
  = FromBigOp sum sum-ext O (! (sumStableUnder (_ , +-is-equiv) (O ∘ φ)))

-- -}
-- -}
-- -}
-- -}
