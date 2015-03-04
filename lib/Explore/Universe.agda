{-# OPTIONS --without-K #-}
open import Level.NP
open import Type
open import Type.Identities
open import Function.NP
open import Function.Extensionality
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Product.NP
open import Data.Sum.NP
open import Data.Sum.Logical
open import Data.Nat
open import Data.Fin
open import Relation.Nullary.NP
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Binary.Logical
open import HoTT using (UA; module Equivalences)
open Equivalences

open import Explore.Core
open import Explore.Properties
open import Explore.Zero
open import Explore.One
open import Explore.Two
open import Explore.Product
open import Explore.Sum
open import Explore.Explorable

module Explore.Universe where

open Operators

module FromX (X : ★) where
  infixr 2 _×ᵁ_

  data U : ★
  El : U → ★

  data U where
    𝟘ᵁ 𝟙ᵁ 𝟚ᵁ : U
    _×ᵁ_ _⊎ᵁ_ : U → U → U
    Σᵁ : (u : U) (f : El u → U) → U
    Xᵁ : U

  El 𝟘ᵁ = 𝟘
  El 𝟙ᵁ = 𝟙
  El 𝟚ᵁ = 𝟚
  El (u₀ ×ᵁ u₁) = El u₀ × El u₁
  El (u₀ ⊎ᵁ u₁) = El u₀ ⊎ El u₁
  El (Σᵁ u f) = Σ (El u) λ x → El (f x)
  El Xᵁ = X

  infix  8 _^ᵁ_
  _^ᵁ_ : U → ℕ → U
  u ^ᵁ zero  = u
  u ^ᵁ suc n = u ×ᵁ u ^ᵁ n

  Finᵁ : ℕ → U
  Finᵁ zero    = 𝟘ᵁ
  Finᵁ (suc n) = 𝟙ᵁ ⊎ᵁ Finᵁ n

  Finᵁ' : ℕ → U
  Finᵁ' zero          = 𝟘ᵁ
  Finᵁ' (suc zero)    = 𝟙ᵁ
  Finᵁ' (suc (suc n)) = 𝟙ᵁ ⊎ᵁ Finᵁ' (suc n)

  Finᵁ-Fin : ∀ n → El (Finᵁ n) ≃ Fin n
  Finᵁ-Fin zero    = ≃-! Fin0≃𝟘
  Finᵁ-Fin (suc n) = ⊎≃ ≃-refl (Finᵁ-Fin n) ≃-∙ ≃-! Fin∘suc≃𝟙⊎Fin

  Finᵁ'-Fin : ∀ n → El (Finᵁ' n) ≃ Fin n
  Finᵁ'-Fin zero          = ≃-! Fin0≃𝟘
  Finᵁ'-Fin (suc zero)    = ≃-! Fin1≃𝟙
  Finᵁ'-Fin (suc (suc n)) = ⊎≃ ≃-refl (Finᵁ'-Fin (suc n)) ≃-∙ ≃-! Fin∘suc≃𝟙⊎Fin

  module From⟦X⟧ (⟦X⟧ : ⟦★₀⟧ X X) where
    data ⟦U⟧ : ⟦★₀⟧ U U
    ⟦El⟧ : (⟦U⟧ ⟦→⟧ ⟦★₀⟧) El El

    data ⟦U⟧ where
      ⟦𝟘ᵁ⟧ : ⟦U⟧ 𝟘ᵁ 𝟘ᵁ
      ⟦𝟙ᵁ⟧ : ⟦U⟧ 𝟙ᵁ 𝟙ᵁ
      ⟦𝟚ᵁ⟧ : ⟦U⟧ 𝟚ᵁ 𝟚ᵁ
      _⟦×ᵁ⟧_ : ⟦Op₂⟧ ⟦U⟧ _×ᵁ_ _×ᵁ_
      _⟦⊎ᵁ⟧_ : ⟦Op₂⟧ ⟦U⟧ _⊎ᵁ_ _⊎ᵁ_
      ⟦Σᵁ⟧ : (⟨ u ∶ ⟦U⟧ ⟩⟦→⟧ (⟦El⟧ u ⟦→⟧ ⟦U⟧) ⟦→⟧ ⟦U⟧) Σᵁ Σᵁ
      ⟦Xᵁ⟧ : ⟦U⟧ Xᵁ Xᵁ

    ⟦El⟧ ⟦𝟘ᵁ⟧ = _≡_
    ⟦El⟧ ⟦𝟙ᵁ⟧ = _≡_
    ⟦El⟧ ⟦𝟚ᵁ⟧ = _≡_
    ⟦El⟧ (u₀ ⟦×ᵁ⟧ u₁) = ⟦El⟧ u₀ ⟦×⟧ ⟦El⟧ u₁
    ⟦El⟧ (u₀ ⟦⊎ᵁ⟧ u₁) = ⟦El⟧ u₀ ⟦⊎⟧ ⟦El⟧ u₁
    ⟦El⟧ (⟦Σᵁ⟧ u f) = ⟦Σ⟧ (⟦El⟧ u) λ x → ⟦El⟧ (f x)
    ⟦El⟧ ⟦Xᵁ⟧ = ⟦X⟧

  module FromXᵉ (Xᵉ : ∀ {ℓ} → Explore ℓ X) where
    explore : ∀ {ℓ} u → Explore ℓ (El u)
    explore 𝟘ᵁ = 𝟘ᵉ
    explore 𝟙ᵁ = 𝟙ᵉ
    explore 𝟚ᵁ = 𝟚ᵉ
    explore (u₀ ×ᵁ u₁) = explore u₀ ×ᵉ explore u₁
    explore (u₀ ⊎ᵁ u₁) = explore u₀ ⊎ᵉ explore u₁
    explore (Σᵁ u f) = exploreΣ (explore u) λ {x} → explore (f x)
    explore Xᵁ = Xᵉ

    module FromXⁱ (Xⁱ : ∀ {ℓ p} → ExploreInd p (Xᵉ {ℓ})) where
      exploreU-ind : ∀ {ℓ p} u → ExploreInd {ℓ} p (explore u)
      exploreU-ind 𝟘ᵁ = 𝟘ⁱ
      exploreU-ind 𝟙ᵁ = 𝟙ⁱ
      exploreU-ind 𝟚ᵁ = 𝟚ⁱ
      exploreU-ind (u₀ ×ᵁ u₁) = exploreU-ind u₀ ×ⁱ exploreU-ind u₁
      exploreU-ind (u₀ ⊎ᵁ u₁) = exploreU-ind u₀ ⊎ⁱ exploreU-ind u₁
      exploreU-ind (Σᵁ u f) = exploreΣ-ind (exploreU-ind u) λ {x} → exploreU-ind (f x)
      exploreU-ind Xᵁ = Xⁱ

      module _ (u : U) where
        private
          uᵉ : ∀ {ℓ} → Explore ℓ (El u)
          uᵉ = explore u
          uⁱ : ∀ {ℓ p} → ExploreInd {ℓ} p uᵉ
          uⁱ = exploreU-ind u

        open FromExploreInd uⁱ public hiding (⟦explore⟧)

        ΣᵉU : ∀ {ℓ} → (El u → ★_ ℓ) → ★_ ℓ
        ΣᵉU = Σᵉ uᵉ
        ΠᵉU : ∀ {ℓ} → (El u → ★_ ℓ) → ★_ ℓ
        ΠᵉU = Πᵉ uᵉ

      module Xᴱ = FromExploreInd Xⁱ
      ΣᵉX : ∀ {ℓ} → (X → ★_ ℓ) → ★_ ℓ
      ΣᵉX = Σᵉ Xᵉ
      ΠᵉX : ∀ {ℓ} → (X → ★_ ℓ) → ★_ ℓ
      ΠᵉX = Πᵉ Xᵉ

      module FromXˢ-ok (Xˢ-ok : Adequate-sum Xᴱ.sum){{_ : UA}}{{_ : FunExt}} where
        adequate-sumU : ∀ u → Adequate-sum (sum u)
        adequate-sumU 𝟘ᵁ       = 𝟘ˢ-ok
        adequate-sumU 𝟙ᵁ       = 𝟙ˢ-ok
        adequate-sumU 𝟚ᵁ       = 𝟚ˢ-ok
        adequate-sumU (u₀ ×ᵁ u₁) = adequate-sumΣ (adequate-sumU u₀) (adequate-sumU u₁)
        adequate-sumU (u₀ ⊎ᵁ u₁) = adequate-sum⊎ (adequate-sumU u₀) (adequate-sumU u₁)
        adequate-sumU (Σᵁ u f) = adequate-sumΣ (adequate-sumU u) (λ {x} → adequate-sumU (f x))
        adequate-sumU Xᵁ = Xˢ-ok

      module FromXˡ (Xˡ : ∀ {ℓ} → Lookup {ℓ} Xᵉ) where
        lookupU : ∀ {ℓ} u → Lookup {ℓ} (explore u)
        lookupU 𝟘ᵁ = 𝟘ˡ
        lookupU 𝟙ᵁ = 𝟙ˡ
        lookupU 𝟚ᵁ = 𝟚ˡ
        lookupU (u₀ ×ᵁ u₁) = lookup× {eᴬ = explore u₀} {eᴮ = explore u₁} (lookupU u₀) (lookupU u₁)
        lookupU (u₀ ⊎ᵁ u₁) = lookup⊎ {eᴬ = explore u₀} {eᴮ = explore u₁} (lookupU u₀) (lookupU u₁)
        lookupU (Σᵁ u f) = lookupΣ {eᴬ = explore u} {eᴮ = λ {x} → explore (f x)} (lookupU u) (λ {x} → lookupU (f x))
        lookupU Xᵁ = Xˡ

      module FromXᶠ (Xᶠ : ∀ {ℓ} → Focus {ℓ} Xᵉ) where
        focusU : ∀ {ℓ} u → Focus {ℓ} (explore u)
        focusU 𝟘ᵁ = 𝟘ᶠ
        focusU 𝟙ᵁ = 𝟙ᶠ
        focusU 𝟚ᵁ = 𝟚ᶠ
        focusU (u₀ ×ᵁ u₁) = focus× {eᴬ = explore u₀} {eᴮ = explore u₁} (focusU u₀) (focusU u₁)
        focusU (u₀ ⊎ᵁ u₁) = focus⊎ {eᴬ = explore u₀} {eᴮ = explore u₁} (focusU u₀) (focusU u₁)
        focusU (Σᵁ u f) = focusΣ {eᴬ = explore u} {eᴮ = λ {x} → explore (f x)} (focusU u) (λ {x} → focusU (f x))
        focusU Xᵁ = Xᶠ

      module FromΣᵉX-ok (ΣᵉX-ok : ∀ {ℓ} → Adequate-Σ {ℓ} ΣᵉX){{_ : UA}}{{_ : FunExt}} where
        ΣᵉU-ok : ∀ {ℓ} u → Adequate-Σ {ℓ} (ΣᵉU u)
        ΣᵉU-ok 𝟘ᵁ       = Σᵉ𝟘-ok
        ΣᵉU-ok 𝟙ᵁ       = Σᵉ𝟙-ok
        ΣᵉU-ok 𝟚ᵁ       = Σᵉ𝟚-ok
        ΣᵉU-ok (u₀ ×ᵁ u) = Σᵉ×-ok {eᴬ = explore u₀} {eᴮ = explore u} (ΣᵉU-ok u₀) (ΣᵉU-ok u)
        ΣᵉU-ok (u₀ ⊎ᵁ u) = Σᵉ⊎-ok {eᴬ = explore u₀} {eᴮ = explore u} (ΣᵉU-ok u₀) (ΣᵉU-ok u)
        ΣᵉU-ok (Σᵁ u f) = ΣᵉΣ-ok {eᴬ = explore u} {eᴮ = λ {x} → explore (f x)} (ΣᵉU-ok u) (λ {x} → ΣᵉU-ok (f x))
        ΣᵉU-ok Xᵁ = ΣᵉX-ok

      module FromΠᵉX-ok (ΠᵉX-ok : ∀ {ℓ} → Adequate-Π {ℓ} ΠᵉX){{_ : UA}}{{_ : FunExt}} where
        ΠᵉU-ok : ∀ {ℓ} u → Adequate-Π {ℓ} (ΠᵉU u)
        ΠᵉU-ok 𝟘ᵁ       = Πᵉ𝟘-ok
        ΠᵉU-ok 𝟙ᵁ       = Πᵉ𝟙-ok
        ΠᵉU-ok 𝟚ᵁ       = Πᵉ𝟚-ok
        ΠᵉU-ok (u₀ ×ᵁ u) = Πᵉ×-ok {eᴬ = explore u₀} {eᴮ = explore u} (ΠᵉU-ok u₀) (ΠᵉU-ok u)
        ΠᵉU-ok (u₀ ⊎ᵁ u) = Πᵉ⊎-ok {eᴬ = explore u₀} {eᴮ = explore u} (ΠᵉU-ok u₀) (ΠᵉU-ok u)
        ΠᵉU-ok (Σᵁ u f) = ΠᵉΣ-ok {eᴬ = explore u} {eᴮ = λ {x} → explore (f x)} (ΠᵉU-ok u) (λ {x} → ΠᵉU-ok (f x))
        ΠᵉU-ok Xᵁ = ΠᵉX-ok

    module From⟦Xᵉ⟧
             {⟦X⟧ : ⟦★₀⟧ X X}
             {ℓ₀ ℓ₁} ℓᵣ
             (⟦Xᵉ⟧ : ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ ⟦X⟧ Xᵉ Xᵉ) where
      open From⟦X⟧ ⟦X⟧ public

      ⟦explore⟧ : ∀ {u₀ u₁} (u : ⟦U⟧ u₀ u₁) → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ (⟦El⟧ u) (explore u₀) (explore u₁)
      ⟦explore⟧ ⟦𝟘ᵁ⟧        = ⟦𝟘ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ}
      ⟦explore⟧ ⟦𝟙ᵁ⟧        = ⟦𝟙ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} {_≡_} {refl}
      ⟦explore⟧ ⟦𝟚ᵁ⟧        = ⟦𝟚ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} {_≡_} {refl} {refl}
      ⟦explore⟧ (u₀ ⟦×ᵁ⟧ u₁) = ⟦explore×⟧ {ℓ₀} {ℓ₁} {ℓᵣ} (⟦explore⟧ u₀) (⟦explore⟧ u₁)
      ⟦explore⟧ (u₀ ⟦⊎ᵁ⟧ u₁) = ⟦explore⊎⟧ {ℓ₀} {ℓ₁} {ℓᵣ} (⟦explore⟧ u₀) (⟦explore⟧ u₁)
      ⟦explore⟧ (⟦Σᵁ⟧ u f)  = ⟦exploreΣ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} (⟦explore⟧ u) (⟦explore⟧ ∘ f)
      ⟦explore⟧ ⟦Xᵁ⟧        = ⟦Xᵉ⟧

    module From⟦Xᵉ⟧≡
             {ℓ₀ ℓ₁} ℓᵣ
             (⟦Xᵉ⟧≡ : ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ _≡_ Xᵉ Xᵉ) where
      open From⟦X⟧ _≡_ public

      ⟦explore⟧≡ : ∀ u → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ _≡_ (explore u) (explore u)
      ⟦explore⟧≡ 𝟘ᵁ        = ⟦𝟘ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ}
      ⟦explore⟧≡ 𝟙ᵁ        = ⟦𝟙ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} {_≡_} {refl}
      ⟦explore⟧≡ 𝟚ᵁ        = ⟦𝟚ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} {_≡_} {refl} {refl}
      ⟦explore⟧≡ (u₀ ×ᵁ u₁) = ⟦explore×⟧≡ {ℓ₀} {ℓ₁} {ℓᵣ} (⟦explore⟧≡ u₀) (⟦explore⟧≡ u₁)
      ⟦explore⟧≡ (u₀ ⊎ᵁ u₁) = ⟦explore⊎⟧≡ {ℓ₀} {ℓ₁} {ℓᵣ} (⟦explore⟧≡ u₀) (⟦explore⟧≡ u₁)
      ⟦explore⟧≡ (Σᵁ u F)  = ⟦exploreΣ⟧≡ {ℓ₀} {ℓ₁} {ℓᵣ} (⟦explore⟧≡ u) (λ x → ⟦explore⟧≡ (F x))
      ⟦explore⟧≡ Xᵁ        = ⟦Xᵉ⟧≡

    module From⟦Xᵉ⟧≡'
             (⟦Xᵉ⟧≡ : ∀ {ℓ₀ ℓ₁} ℓᵣ → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ _≡_ Xᵉ Xᵉ)
             (u : U) {{_ : FunExt}}{{_ : UA}} where
      open From⟦Explore⟧ (λ {ℓ₁} {ℓ₂} ℓᵣ → From⟦Xᵉ⟧≡.⟦explore⟧≡ {ℓ₁} {ℓ₂} ℓᵣ (⟦Xᵉ⟧≡ ℓᵣ) u) public

module FromKit
   {X : ★}
   {Xᵉ : ∀ {ℓ} → Explore ℓ X}
   (Xⁱ : ∀ {ℓ p} → ExploreInd p (Xᵉ {ℓ}))
   (let module Xᴱ = FromExploreInd Xⁱ)
   (Xˢ-ok : ∀{{_ : UA}}{{_ : FunExt}} → Adequate-sum Xᴱ.sum)
   (Xˡ : ∀ {ℓ} → Lookup {ℓ} Xᵉ)
   (Xᶠ : ∀ {ℓ} → Focus {ℓ} Xᵉ)
   (ΣᵉX-ok : ∀{{_ : UA}}{{_ : FunExt}}{ℓ} → Adequate-Σ {ℓ} (Σᵉ Xᵉ))
   (ΠᵉX-ok : ∀{{_ : UA}}{{_ : FunExt}}{ℓ} → Adequate-Π {ℓ} (Πᵉ Xᵉ))
   (⟦Xᵉ⟧≡ : ∀ {ℓ₀ ℓ₁} ℓᵣ → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ _≡_ Xᵉ Xᵉ)
   where

  open FromX X public
  open FromXᵉ Xᵉ public
  open FromXⁱ Xⁱ public
  open FromXˡ Xˡ public
  open FromXᶠ Xᶠ public

  module _ {{_ : FunExt}}{{_ : UA}} where
    open FromXˢ-ok Xˢ-ok public
    open FromΣᵉX-ok ΣᵉX-ok public
    open FromΠᵉX-ok ΠᵉX-ok public
    open From⟦Xᵉ⟧≡' ⟦Xᵉ⟧≡ public

    module _ (u : U) where
      open FromAdequate-Σᵉ u (ΣᵉU-ok u) public
      open FromAdequate-Πᵉ u (ΠᵉU-ok u) public

      module _ (P : El u → ★₀) where
        Dec-Σ : Π (El u) (Dec ∘ P) → Dec (Σ (El u) P)
        Dec-Σ = Dec-Σ.Dec-Σ u (focusU u) P
