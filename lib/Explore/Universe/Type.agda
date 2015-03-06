{-# OPTIONS --without-K #-}
open import Type using (Type₀; Type₁)
open import Type.Identities
open import Data.Zero using (𝟘)
open import Data.One using (𝟙; 0₁)
open import Data.Two.Base using (𝟚; 0₂; 1₂)
open import Data.Product.NP using (Σ; _×_)
open import Data.Sum.NP using (_⊎_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import HoTT using (ua; UA; module Equivalences)
open        Equivalences using (_≃_; ≃-!; ≃-refl; _≃-∙_)

module Explore.Universe.Type {X : Type₀} where

infixr 2 _×ᵁ_

data U : Type₁
El : U → Type₀

data U where
  𝟘ᵁ 𝟙ᵁ 𝟚ᵁ : U
  _×ᵁ_ _⊎ᵁ_ : U → U → U
  Σᵁ : (u : U) (f : El u → U) → U
  Xᵁ : U
  ≃ᵁ : (u : U) (A : Type₀) (e : El u ≃ A) → U

El 𝟘ᵁ = 𝟘
El 𝟙ᵁ = 𝟙
El 𝟚ᵁ = 𝟚
El (u₀ ×ᵁ u₁) = El u₀ × El u₁
El (u₀ ⊎ᵁ u₁) = El u₀ ⊎ El u₁
El (Σᵁ u f) = Σ (El u) λ x → El (f x)
El Xᵁ = X
El (≃ᵁ u A e) = A

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
