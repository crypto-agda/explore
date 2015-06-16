{-# OPTIONS --without-K #-}
open import Type using (Type₀; Type_)
open import Type.Identities
open import Function.NP using (Π; _∘_; const)
open import Function.Extensionality using (FunExt)
open import Data.One using (0₁)
open import Data.Two.Base using (0₂; 1₂)
open import Data.Product.NP using (_,_; fst)
open import Data.Sum.NP using (inl; inr)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; idp; ap; !_; _∙_; tr)
open import HoTT using (ua; UA; module Equivalences)
open        Equivalences using (_≃_)

open import Explore.Core
open import Explore.Zero
open import Explore.One
open import Explore.Two
open import Explore.Product
open        Explore.Product.Operators
open import Explore.Sum
open import Explore.Properties
open import Explore.Explorable
open import Explore.Isomorphism
import      Explore.Universe.Type

module Explore.Universe.FromE
  (X : Type₀) (Xᵉ : ∀ {ℓ} → Explore ℓ X) where

open Explore.Universe.Type {X}

explore : ∀ {ℓ} u → Explore ℓ (El u)
explore 𝟘ᵁ = 𝟘ᵉ
explore 𝟙ᵁ = 𝟙ᵉ
explore 𝟚ᵁ = 𝟚ᵉ
explore (u₀ ×ᵁ u₁) = explore u₀ ×ᵉ explore u₁
explore (u₀ ⊎ᵁ u₁) = explore u₀ ⊎ᵉ explore u₁
explore (Σᵁ u f) = exploreΣ (explore u) λ {x} → explore (f x)
explore Xᵁ = Xᵉ
explore (≃ᵁ u A e) = explore-iso e (explore u)

module FromXⁱ (Xⁱ : ∀ {ℓ p} → ExploreInd p (Xᵉ {ℓ})) where
  explore-ind : ∀ {ℓ p} u → ExploreInd {ℓ} p (explore u)
  explore-ind 𝟘ᵁ = 𝟘ⁱ
  explore-ind 𝟙ᵁ = 𝟙ⁱ
  explore-ind 𝟚ᵁ = 𝟚ⁱ
  explore-ind (u₀ ×ᵁ u₁) = explore-ind u₀ ×ⁱ explore-ind u₁
  explore-ind (u₀ ⊎ᵁ u₁) = explore-ind u₀ ⊎ⁱ explore-ind u₁
  explore-ind (Σᵁ u f) = exploreΣ-ind (explore-ind u) λ {x} → explore-ind (f x)
  explore-ind Xᵁ = Xⁱ
  explore-ind (≃ᵁ u A e) = explore-iso-ind e (explore-ind u)

  module _ (u : U) where
    private
      uᵉ : ∀ {ℓ} → Explore ℓ (El u)
      uᵉ = explore u
      uⁱ : ∀ {ℓ p} → ExploreInd {ℓ} p uᵉ
      uⁱ = explore-ind u

    open FromExploreInd uⁱ public hiding (⟦explore⟧)

    ΣᵉU : ∀ {ℓ} → (El u → Type ℓ) → Type ℓ
    ΣᵉU = Σᵉ uᵉ
    ΠᵉU : ∀ {ℓ} → (El u → Type ℓ) → Type ℓ
    ΠᵉU = Πᵉ uᵉ

  module Xᴱ = FromExploreInd Xⁱ
  ΣᵉX : ∀ {ℓ} → (X → Type ℓ) → Type ℓ
  ΣᵉX = Σᵉ Xᵉ
  ΠᵉX : ∀ {ℓ} → (X → Type ℓ) → Type ℓ
  ΠᵉX = Πᵉ Xᵉ

  open Adequacy _≡_
  module FromXˢ-ok (Xˢ-ok : Adequate-sum Xᴱ.sum){{_ : UA}}{{_ : FunExt}} where
    adequate-sum : ∀ u → Adequate-sum (sum u)
    adequate-sum 𝟘ᵁ       = 𝟘ˢ-ok
    adequate-sum 𝟙ᵁ       = 𝟙ˢ-ok
    adequate-sum 𝟚ᵁ       = 𝟚ˢ-ok
    adequate-sum (u₀ ×ᵁ u₁) = adequate-sumΣ (adequate-sum u₀) (adequate-sum u₁)
    adequate-sum (u₀ ⊎ᵁ u₁) = adequate-sum⊎ (adequate-sum u₀) (adequate-sum u₁)
    adequate-sum (Σᵁ u f) = adequate-sumΣ (adequate-sum u) (λ {x} → adequate-sum (f x))
    adequate-sum Xᵁ = Xˢ-ok
    adequate-sum (≃ᵁ u A e) = sum-iso-ok e (adequate-sum u)

  module FromXˡ (Xˡ : ∀ {ℓ} → Lookup {ℓ} Xᵉ) where
    lookup : ∀ {ℓ} u → Lookup {ℓ} (explore u)
    lookup 𝟘ᵁ = 𝟘ˡ
    lookup 𝟙ᵁ = 𝟙ˡ
    lookup 𝟚ᵁ = 𝟚ˡ
    lookup (u₀ ×ᵁ u₁) = lookup× {eᴬ = explore u₀} {eᴮ = explore u₁} (lookup u₀) (lookup u₁)
    lookup (u₀ ⊎ᵁ u₁) = lookup⊎ {eᴬ = explore u₀} {eᴮ = explore u₁} (lookup u₀) (lookup u₁)
    lookup (Σᵁ u f) = lookupΣ {eᴬ = explore u} {eᴮ = λ {x} → explore (f x)} (lookup u) (λ {x} → lookup (f x))
    lookup Xᵁ = Xˡ
    lookup (≃ᵁ u A e) = lookup-iso e {Aᵉ = explore u} (lookup u)

  module FromXᶠ (Xᶠ : ∀ {ℓ} → Focus {ℓ} Xᵉ) where
    focus : ∀ {ℓ} u → Focus {ℓ} (explore u)
    focus 𝟘ᵁ = 𝟘ᶠ
    focus 𝟙ᵁ = 𝟙ᶠ
    focus 𝟚ᵁ = 𝟚ᶠ
    focus (u₀ ×ᵁ u₁) = focus× {eᴬ = explore u₀} {eᴮ = explore u₁} (focus u₀) (focus u₁)
    focus (u₀ ⊎ᵁ u₁) = focus⊎ {eᴬ = explore u₀} {eᴮ = explore u₁} (focus u₀) (focus u₁)
    focus (Σᵁ u f) = focusΣ {eᴬ = explore u} {eᴮ = λ {x} → explore (f x)} (focus u) (λ {x} → focus (f x))
    focus Xᵁ = Xᶠ
    focus (≃ᵁ u A e) = focus-iso e {Aᵉ = explore u} (focus u)

  module FromΣᵉX-ok (ΣᵉX-ok : ∀ {ℓ} → Adequate-Σ {ℓ} ΣᵉX){{_ : UA}}{{_ : FunExt}} where
    Σᵉ-ok : ∀ {ℓ} u → Adequate-Σ {ℓ} (ΣᵉU u)
    Σᵉ-ok 𝟘ᵁ       = Σᵉ𝟘-ok
    Σᵉ-ok 𝟙ᵁ       = Σᵉ𝟙-ok
    Σᵉ-ok 𝟚ᵁ       = Σᵉ𝟚-ok
    Σᵉ-ok (u₀ ×ᵁ u) = Σᵉ×-ok {eᴬ = explore u₀} {eᴮ = explore u} (Σᵉ-ok u₀) (Σᵉ-ok u)
    Σᵉ-ok (u₀ ⊎ᵁ u) = Σᵉ⊎-ok {eᴬ = explore u₀} {eᴮ = explore u} (Σᵉ-ok u₀) (Σᵉ-ok u)
    Σᵉ-ok (Σᵁ u f) = ΣᵉΣ-ok {eᴬ = explore u} {eᴮ = λ {x} → explore (f x)} (Σᵉ-ok u) (λ {x} → Σᵉ-ok (f x))
    Σᵉ-ok Xᵁ = ΣᵉX-ok
    Σᵉ-ok (≃ᵁ u A e) = Σ-iso-ok e {Aᵉ = explore u} (Σᵉ-ok u)

  module FromΠᵉX-ok (ΠᵉX-ok : ∀ {ℓ} → Adequate-Π {ℓ} ΠᵉX){{_ : UA}}{{_ : FunExt}} where
    Πᵉ-ok : ∀ {ℓ} u → Adequate-Π {ℓ} (ΠᵉU u)
    Πᵉ-ok 𝟘ᵁ       = Πᵉ𝟘-ok
    Πᵉ-ok 𝟙ᵁ       = Πᵉ𝟙-ok
    Πᵉ-ok 𝟚ᵁ       = Πᵉ𝟚-ok
    Πᵉ-ok (u₀ ×ᵁ u) = Πᵉ×-ok {eᴬ = explore u₀} {eᴮ = explore u} (Πᵉ-ok u₀) (Πᵉ-ok u)
    Πᵉ-ok (u₀ ⊎ᵁ u) = Πᵉ⊎-ok {eᴬ = explore u₀} {eᴮ = explore u} (Πᵉ-ok u₀) (Πᵉ-ok u)
    Πᵉ-ok (Σᵁ u f) = ΠᵉΣ-ok {eᴬ = explore u} {eᴮ = λ {x} → explore (f x)} (Πᵉ-ok u) (λ {x} → Πᵉ-ok (f x))
    Πᵉ-ok Xᵁ = ΠᵉX-ok
    Πᵉ-ok (≃ᵁ u A e) = Π-iso-ok e {Aᵉ = explore u} (Πᵉ-ok u)

module From⟦Xᵉ⟧≡ (⟦Xᵉ⟧≡ : ∀ {ℓ₀ ℓ₁} ℓᵣ → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ _≡_ Xᵉ Xᵉ) {ℓ₀ ℓ₁} ℓᵣ where
  ⟦explore⟧≡ : ∀ u → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ _≡_ (explore u) (explore u)
  ⟦explore⟧≡ 𝟘ᵁ        = ⟦𝟘ᵉ⟧ {ℓᵣ = ℓᵣ}
  ⟦explore⟧≡ 𝟙ᵁ        = ⟦𝟙ᵉ⟧ {ℓᵣ = ℓᵣ} {_≡_} {idp}
  ⟦explore⟧≡ 𝟚ᵁ        = ⟦𝟚ᵉ⟧ {ℓᵣ = ℓᵣ} {_≡_} {idp} {idp}
  ⟦explore⟧≡ (u₀ ×ᵁ u₁) = ⟦explore×⟧≡ {ℓᵣ = ℓᵣ} (⟦explore⟧≡ u₀) (⟦explore⟧≡ u₁)
  ⟦explore⟧≡ (u₀ ⊎ᵁ u₁) = ⟦explore⊎⟧≡ {ℓᵣ = ℓᵣ} (⟦explore⟧≡ u₀) (⟦explore⟧≡ u₁)
  ⟦explore⟧≡ (Σᵁ u F)  = ⟦exploreΣ⟧≡ {ℓᵣ = ℓᵣ} (⟦explore⟧≡ u) (λ x → ⟦explore⟧≡ (F x))
  ⟦explore⟧≡ Xᵁ        = ⟦Xᵉ⟧≡ ℓᵣ
  ⟦explore⟧≡ (≃ᵁ u A e) = ⟦explore-iso⟧ e {ℓᵣ = ℓᵣ} (ap (fst e)) (⟦explore⟧≡ u)

module FromΠX (ΠX : (X → U) → U) where
  Πᵁ : (u : U) (v : El u → U) → U
  Πᵁ 𝟘ᵁ        v = 𝟙ᵁ
  Πᵁ 𝟙ᵁ        v = v _
  Πᵁ 𝟚ᵁ        v = v 0₂ ×ᵁ v 1₂
  Πᵁ (u ×ᵁ u₁) v = Πᵁ u λ x → Πᵁ u₁ λ y → v (x , y)
  Πᵁ (u ⊎ᵁ u₁) v = (Πᵁ u (v ∘ inl)) ×ᵁ (Πᵁ u₁ (v ∘ inr))
  Πᵁ (Σᵁ u f)  v = Πᵁ u λ x → Πᵁ (f x) (v ∘ _,_ x)
  Πᵁ Xᵁ        v = ΠX v
  Πᵁ (≃ᵁ u A e)v = Πᵁ u (v ∘ fst e)

  _→ᵁ_ : (u : U) (v : U) → U
  u →ᵁ v = Πᵁ u (const v)

  module FromΠX≃ (ΠX≃ : ∀ v → El (ΠX v) ≃ Π X (El ∘ v)) where
    private
      module ΠX≃ {v} = Equivalences.Equiv (ΠX≃ v)

    module _ {{_ : FunExt}}{{_ : UA}} where
      Πᵁ-Π : ∀ u v → El (Πᵁ u v) ≡ Π (El u) (El ∘ v)
      Πᵁ-Π 𝟘ᵁ        v = ! Π𝟘-uniq₀ _
      Πᵁ-Π 𝟙ᵁ        v = ! Π𝟙-uniq _
      Πᵁ-Π 𝟚ᵁ        v = ! Π𝟚-×
      Πᵁ-Π (u ×ᵁ u₁) v = Πᵁ-Π u (λ x → Πᵁ u₁ (v ∘ _,_ x)) ∙ Π=′ _ (λ _ → Πᵁ-Π u₁ _) ∙ ! ΠΣ-curry
      Πᵁ-Π (u ⊎ᵁ u₁) v = ×= (Πᵁ-Π u (v ∘ inl)) (Πᵁ-Π u₁ (v ∘ inr)) ∙ ! dist-×-Π
      Πᵁ-Π (Σᵁ u f)  v = Πᵁ-Π u (λ x → Πᵁ (f _) (v ∘ _,_ x)) ∙ Π=′ _ (λ _ → Πᵁ-Π (f _) _) ∙ ! ΠΣ-curry
      Πᵁ-Π Xᵁ        v = ua (ΠX≃ v)
      Πᵁ-Π (≃ᵁ u A e)v = Πᵁ-Π u (v ∘ fst e) ∙ Π≃ e λ _ → idp

      →ᵁ-→ : ∀ u v → El (u →ᵁ v) ≡ (El u → El v)
      →ᵁ-→ u v = Πᵁ-Π u (const v)

    Πᵁ→Π : ∀ u v → El (Πᵁ u v) → Π (El u) (El ∘ v)
    Πᵁ→Π 𝟘ᵁ v x₂ ()
    Πᵁ→Π 𝟙ᵁ v x₂ x₃ = x₂
    Πᵁ→Π 𝟚ᵁ v (x , y) 0₂ = x
    Πᵁ→Π 𝟚ᵁ v (x , y) 1₂ = y
    Πᵁ→Π (u ×ᵁ u₁) v x (z , t) = Πᵁ→Π u₁ (v ∘ _,_ z) (Πᵁ→Π u (λ x → Πᵁ u₁ (v ∘ _,_ x)) x z) t
    Πᵁ→Π (u ⊎ᵁ _) v (x , _) (inl y) = Πᵁ→Π u (v ∘ inl) x y
    Πᵁ→Π (_ ⊎ᵁ u) v (_ , x) (inr y) = Πᵁ→Π u (v ∘ inr) x y
    Πᵁ→Π (Σᵁ u f) v x       (y , z) = Πᵁ→Π (f _) (v ∘ _,_ y) (Πᵁ→Π u (λ x → Πᵁ (f _) (v ∘ _,_ x)) x y) z
    Πᵁ→Π Xᵁ v = ΠX≃.·→
    Πᵁ→Π (≃ᵁ u A e) v f x = tr (El ∘ v) (·←-inv-r x) (Πᵁ→Π u (v ∘ ·→) f (·← x))
      where open Equivalences.Equiv e

    Π→Πᵁ : ∀ u v → Π (El u) (El ∘ v) → El (Πᵁ u v)
    Π→Πᵁ 𝟘ᵁ v f = 0₁
    Π→Πᵁ 𝟙ᵁ v f = f 0₁
    Π→Πᵁ 𝟚ᵁ v f = f 0₂ , f 1₂
    Π→Πᵁ (u ×ᵁ u₁) v f = Π→Πᵁ u (λ x → Πᵁ u₁ (v ∘ _,_ x))
                           (λ x → Π→Πᵁ u₁ (v ∘ _,_ x) (f ∘ _,_ x))
    Π→Πᵁ (u ⊎ᵁ u₁) v f = Π→Πᵁ u (v ∘ inl) (f ∘ inl) ,
                           Π→Πᵁ u₁ (v ∘ inr) (f ∘ inr)
    Π→Πᵁ (Σᵁ u F) v f = Π→Πᵁ u (λ x → Πᵁ (F x) (v ∘ _,_ x))
                          (λ x → Π→Πᵁ (F x) (v ∘ _,_ x) (f ∘ _,_ x))
    Π→Πᵁ Xᵁ v = ΠX≃.·←
    Π→Πᵁ (≃ᵁ u A e) v f = Π→Πᵁ u (v ∘ ·→) (f ∘ ·→)
      where open Equivalences.Equiv e

    →ᵁ→→ : ∀ u v → El (u →ᵁ v) → (El u → El v)
    →ᵁ→→ u v = Πᵁ→Π u (const v)

    →→→ᵁ : ∀ u v → (El u → El v) → El (u →ᵁ v)
    →→→ᵁ u v = Π→Πᵁ u (const v)
