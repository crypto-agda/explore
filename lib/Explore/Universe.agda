{-# OPTIONS --without-K #-}
open import Type using (Type₀; Type₁; Type_)
open import Type.Identities
open import Function.NP using (Π; _∘_; const)
open import Function.Extensionality using (FunExt)
open import Data.Zero using (𝟘)
open import Data.One using (𝟙; 0₁)
open import Data.Two.Base using (𝟚; 0₂; 1₂)
open import Data.Product.NP using (Σ; _×_; _,_; fst; snd)
open import Data.Sum.NP using (_⊎_; inl; inr)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Relation.Nullary.NP using (Dec)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; idp; ap; !_; _∙_; tr)
open import HoTT using (ua; UA; module Equivalences)
open        Equivalences using (_≃_; ≃-!; ≃-refl; _≃-∙_)

open import Explore.Core
open import Explore.Properties
open import Explore.Zero
open import Explore.One
open import Explore.Two
open import Explore.Product
open        Explore.Product.Operators
open import Explore.Sum
open import Explore.Explorable
open import Explore.Isomorphism
open import Explore.GuessingGameFlipping
import      Explore.Universe.Type
import      Explore.Universe.FromE

module Explore.Universe (X : Type₀) where

open Explore.Universe.Type {X}

module FromXᵉ = Explore.Universe.FromE X

open Adequacy _≡_
module FromKit
    {Xᵉ : ∀ {ℓ} → Explore ℓ X}
    (Xⁱ : ∀ {ℓ p} → ExploreInd p (Xᵉ {ℓ}))
    (let module Xᴱ = FromExploreInd Xⁱ)
    (Xˢ-ok : ∀{{_ : UA}}{{_ : FunExt}} → Adequate-sum Xᴱ.sum)
    (Xˡ : ∀ {ℓ} → Lookup {ℓ} Xᵉ)
    (Xᶠ : ∀ {ℓ} → Focus {ℓ} Xᵉ)
    (ΣᵉX-ok : ∀{{_ : UA}}{{_ : FunExt}}{ℓ} → Adequate-Σ {ℓ} (Σᵉ Xᵉ))
    (ΠᵉX-ok : ∀{{_ : UA}}{{_ : FunExt}}{ℓ} → Adequate-Π {ℓ} (Πᵉ Xᵉ))
    (⟦Xᵉ⟧≡ : ∀ {ℓ₀ ℓ₁} ℓᵣ → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ _≡_ Xᵉ Xᵉ)
    (ΠX : (X → U) → U)
    (ΠX≃ : ∀{{_ : UA}}{{_ : FunExt}} v → El (ΠX v) ≃ Π X (El ∘ v))
    (u : U)
  where

  private
   module M where
    open FromXᵉ Xᵉ public
    open FromXⁱ Xⁱ public
    open FromXˡ Xˡ public
    open FromXᶠ Xᶠ public
    open FromΠX ΠX public

    module _ {{_ : FunExt}}{{_ : UA}} where
      open FromΣᵉX-ok ΣᵉX-ok public
      open FromΠᵉX-ok ΠᵉX-ok public
      open From⟦Xᵉ⟧≡  ⟦Xᵉ⟧≡  public
      open FromΠX≃   ΠX≃ public

  explore : ∀ {ℓ} → Explore ℓ (El u)
  explore = M.explore u

  explore-ind : ∀ {ℓ p} → ExploreInd {ℓ} p explore
  explore-ind = M.explore-ind u

  open FromExploreInd explore-ind public hiding (⟦explore⟧)
  -- TODO list what is exported here

  lookup : ∀ {ℓ} → Lookup {ℓ} explore
  lookup = M.lookup u

  open FromLookup {explore = explore} lookup public

  focus : ∀ {ℓ} → Focus {ℓ} explore
  focus = M.focus u

  Πᵁ : (v : El u → U) → U
  Πᵁ = M.Πᵁ u

  _→ᵁ_ : (v : U) → U
  _→ᵁ_ = M._→ᵁ_ u

  module _ {{_ : FunExt}}{{_ : UA}} where
    Σᵉ-ok : ∀ {ℓ} → Adequate-Σ {ℓ} (Σᵉ explore)
    Σᵉ-ok = M.Σᵉ-ok u

    Πᵉ-ok : ∀ {ℓ} → Adequate-Π {ℓ} (Πᵉ explore)
    Πᵉ-ok = M.Πᵉ-ok u

    ⟦explore⟧≡ : ∀ {ℓ₀ ℓ₁} ℓᵣ → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ _≡_ explore explore
    ⟦explore⟧≡ ℓᵣ = M.⟦explore⟧≡ ℓᵣ u

    open From⟦Explore⟧ ⟦explore⟧≡ public
      using ( sum⇒Σᵉ
            ; product⇒Πᵉ
            ; ✓all-Πᵉ
            ; ✓any→Σᵉ
            ; module FromAdequate-Σᵉ
            ; module FromAdequate-Πᵉ
            )

    open FromAdequate-Σᵉ Σᵉ-ok public
      using ( sumStableUnder
            ; sumStableUnder′
            ; same-count→iso
            ; adequate-sum
            ; adequate-any
            )

    open FromAdequate-Πᵉ Πᵉ-ok public
      using ( adequate-product
            ; adequate-all
            ; check!
            )

    Dec-Σ : ∀ {p}{P : El u → Type p} → Π (El u) (Dec ∘ P) → Dec (Σ (El u) P)
    Dec-Σ = FromFocus.Dec-Σ focus

    Πᵁ-Π : ∀ v → El (Πᵁ v) ≡ Π (El u) (El ∘ v)
    Πᵁ-Π = M.Πᵁ-Π u

    →ᵁ-→ : ∀ v → El (_→ᵁ_ v) ≡ (El u → El v)
    →ᵁ-→ = M.→ᵁ-→ u

    Πᵁ→Π : ∀ v → El (Πᵁ v) → Π (El u) (El ∘ v)
    Πᵁ→Π = M.Πᵁ→Π u

    Π→Πᵁ : ∀ v → Π (El u) (El ∘ v) → El (Πᵁ v)
    Π→Πᵁ = M.Π→Πᵁ u

    →ᵁ→→ : ∀ v → El (_→ᵁ_ v) → (El u → El v)
    →ᵁ→→ = M.→ᵁ→→ u

    →→→ᵁ : ∀ v → (El u → El v) → El (_→ᵁ_ v)
    →→→ᵁ = M.→→→ᵁ u

    guessing-game-flipping = Explore.GuessingGameFlipping.thm (El u) sum sum-ind
-- -}
-- -}
-- -}
-- -}
-- -}
