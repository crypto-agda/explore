open import Level.NP
open import Type
open import Relation.Binary.Logical
open import Relation.Binary.PropositionalEquality

module Explore.Universe.Logical (X : ★) where

open import Explore.Universe.Type
open import Explore.Universe X
open import Explore.Core

module From⟦X⟧ (⟦X⟧ : ⟦★₀⟧ X X) where

  -- TODO _⟦≃⟧_ : (⟦Rel⟧ ⟦★₀⟧) ₀ _≃_ _≃_

  data ⟦U⟧ : ⟦★₁⟧ U U
  ⟦El⟧ : (⟦U⟧ ⟦→⟧ ⟦★₀⟧) El El

  data ⟦U⟧ where
    ⟦𝟘ᵁ⟧ : ⟦U⟧ 𝟘ᵁ 𝟘ᵁ
    ⟦𝟙ᵁ⟧ : ⟦U⟧ 𝟙ᵁ 𝟙ᵁ
    ⟦𝟚ᵁ⟧ : ⟦U⟧ 𝟚ᵁ 𝟚ᵁ
    _⟦×ᵁ⟧_ : ⟦Op₂⟧ {_} {_} {₁} ⟦U⟧ _×ᵁ_ _×ᵁ_
    _⟦⊎ᵁ⟧_ : ⟦Op₂⟧ {_} {_} {₁} ⟦U⟧ _⊎ᵁ_ _⊎ᵁ_
    ⟦Σᵁ⟧ : (⟨ u ∶ ⟦U⟧ ⟩⟦→⟧ (⟦El⟧ u ⟦→⟧ ⟦U⟧) ⟦→⟧ ⟦U⟧) Σᵁ Σᵁ
    ⟦Xᵁ⟧ : ⟦U⟧ Xᵁ Xᵁ
    -- ⟦≃ᵁ⟧ : (⟨ u ∶ ⟦U⟧ ⟩⟦→⟧ (⟨ A ∶ ⟦★₀⟧ ⟩⟦→⟧ ⟦El⟧ u ⟦≃⟧ A ⟦→⟧ ⟦U⟧)) ≃ᵁ ≃ᵁ

  ⟦El⟧ ⟦𝟘ᵁ⟧ = _≡_
  ⟦El⟧ ⟦𝟙ᵁ⟧ = _≡_
  ⟦El⟧ ⟦𝟚ᵁ⟧ = _≡_
  ⟦El⟧ (u₀ ⟦×ᵁ⟧ u₁) = ⟦El⟧ u₀ ⟦×⟧ ⟦El⟧ u₁
  ⟦El⟧ (u₀ ⟦⊎ᵁ⟧ u₁) = ⟦El⟧ u₀ ⟦⊎⟧ ⟦El⟧ u₁
  ⟦El⟧ (⟦Σᵁ⟧ u f) = ⟦Σ⟧ (⟦El⟧ u) λ x → ⟦El⟧ (f x)
  ⟦El⟧ ⟦Xᵁ⟧ = ⟦X⟧
  -- ⟦El⟧ (⟦≃ᵁ⟧ u A e) = A

  module From⟦Xᵉ⟧
           {⟦X⟧ : ⟦★₀⟧ X X}
           {ℓ₀ ℓ₁} ℓᵣ
           {Xᵉ : Explore X}
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
    -- ⟦explore⟧ (⟦≃ᵁ⟧ u A e) = {!⟦explore-iso⟧ e!}


{-
⟦U⟧-sound : ∀ {{_ : FunExt}} {x y} → ⟦U⟧ x y → x ≡ y
⟦U⟧-refl : ∀ x → ⟦U⟧ x x

{-
⟦El⟧-refl : ∀ x → {!⟦El⟧ x x!}
⟦El⟧-refl = {!!}
-}

⟦U⟧-sound ⟦𝟘ᵁ⟧ = refl
⟦U⟧-sound ⟦𝟙ᵁ⟧ = refl
⟦U⟧-sound ⟦𝟚ᵁ⟧ = refl
⟦U⟧-sound (u ⟦×ᵁ⟧ u₁) = ap₂ _×ᵁ_ (⟦U⟧-sound u) (⟦U⟧-sound u₁)
⟦U⟧-sound (u ⟦⊎ᵁ⟧ u₁) = ap₂ _⊎ᵁ_ (⟦U⟧-sound u) (⟦U⟧-sound u₁)
⟦U⟧-sound (⟦Σᵁ⟧ {u₀} {u₁} u {f₀} {f₁} fᵣ) = apd₂ Σᵁ (⟦U⟧-sound u) (tr-→ El (const U) (⟦U⟧-sound u) f₀ ∙ λ= (λ A → ap (λ z → z (f₀ (tr El (! ⟦U⟧-sound u) A))) (tr-const (⟦U⟧-sound u)) ∙ ⟦U⟧-sound (fᵣ {!!}))) -- (λ= (λ y → let foo = xᵣ {{!!}} {y} {!xᵣ!} in {!tr-→ El (const U) (⟦U⟧-sound u)!}))

⟦U⟧-refl 𝟘ᵁ = ⟦𝟘ᵁ⟧
⟦U⟧-refl 𝟙ᵁ = ⟦𝟙ᵁ⟧
⟦U⟧-refl 𝟚ᵁ = ⟦𝟚ᵁ⟧
⟦U⟧-refl (x ×ᵁ x₁) = ⟦U⟧-refl x ⟦×ᵁ⟧ ⟦U⟧-refl x₁
⟦U⟧-refl (x ⊎ᵁ x₁) = ⟦U⟧-refl x ⟦⊎ᵁ⟧ ⟦U⟧-refl x₁
⟦U⟧-refl (Σᵁ x f) = ⟦Σᵁ⟧ (⟦U⟧-refl x) (λ y → {!⟦U⟧-refl ?!})
-}
