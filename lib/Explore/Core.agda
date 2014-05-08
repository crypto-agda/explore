{-# OPTIONS --without-K #-}
-- The core types behind exploration functions
module Explore.Core where

open import Level.NP
open import Algebra
open import Type hiding (★)
open import Function using (id; _∘_; _∘′_)
open import Data.Nat.NP using (ℕ)
open import Data.Two using (𝟚)
open import Data.Maybe.NP using (_→?_)
open import Relation.Unary.Logical
open import Relation.Binary.Logical

BigOp : ∀ {ℓ} → ★ ℓ → ★₀ → ★ ℓ
BigOp M A = (A → M) → M

Explore : ∀ ℓ → ★₀ → ★ ₛ ℓ
Explore ℓ A = ∀ {M : ★ ℓ} (ε : M) (_∙_ : M → M → M) → BigOp M A

BigOpMon : ∀ {c ℓ} → Monoid c ℓ → ★₀ → ★ _
BigOpMon M A = BigOp (Monoid.Carrier M) A

ExploreMon : ∀ c ℓ → ★₀ → ★ _
ExploreMon c ℓ A = (M : Monoid c ℓ) → BigOpMon M A

Explore₀ : ★₀ → ★₁
Explore₀ = Explore _

Explore₁ : ★₀ → ★₂
Explore₁ = Explore _

Sum : ★₀ → ★₀
Sum = BigOp ℕ

Product : ★₀ → ★₀
Product = BigOp ℕ

Count : ★₀ → ★₀
Count A = (A → 𝟚) → ℕ

Find? : ★₀ → ★₁
Find? A = ∀ {B : ★₀} → (A →? B) →? B

FindKey : ★₀ → ★₀
FindKey A = (A → 𝟚) →? A

[Explore] : ∀ a aₚ → ([★₀] [→] [★] (ₛ (a ⊔ aₚ))) (Explore a)
[Explore] a aₚ Aₚ = ∀⟨ Mₚ ∶ [★] (a ⊔ aₚ)⟩[→] Mₚ [→] [Op₂] {_} {aₚ} Mₚ [→] (Aₚ [→] Mₚ) [→] Mₚ

⟦Explore⟧ : (⟦★₀⟧ ⟦→⟧ ⟦★₁⟧) (Explore _) (Explore _)
⟦Explore⟧ Aᵣ = ∀⟨ Mᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ Mᵣ ⟦→⟧ ⟦Op₂⟧ Mᵣ ⟦→⟧ (Aᵣ ⟦→⟧ Mᵣ) ⟦→⟧ Mᵣ

⟦Explore⟧ᵤ : ∀ a₁ a₂ aᵣ → (⟦★₀⟧ ⟦→⟧ ⟦★⟧ (ₛ (a₁ ⊔ a₂ ⊔ aᵣ))) (Explore a₁) (Explore a₂)
⟦Explore⟧ᵤ a₁ a₂ aᵣ Aᵣ = ∀⟨ Mᵣ ∶ ⟦★⟧ (aᵣ ⊔ a₁ ⊔ a₂) ⟩⟦→⟧ Mᵣ ⟦→⟧ ⟦Op₂⟧ {_} {_} {aᵣ} Mᵣ ⟦→⟧ (Aᵣ ⟦→⟧ Mᵣ) ⟦→⟧ Mᵣ

-- Trimmed down version of ⟦Explore⟧
⟦Explore⟧₁ : ∀ {A : ★_ _} (Aᵣ : A → A → ★_ _) → Explore _ A → ★₁
⟦Explore⟧₁ Aᵣ e = ⟦Explore⟧ Aᵣ e e

-- These three basic combinators are defined here
-- since they are used to define ExploreInd
module _ {ℓ A} where
    merge-explore : Explore ℓ A → Explore ℓ A → Explore ℓ A
    merge-explore e₀ e₁ ε _∙_ f = e₀ ε _∙_ f ∙ e₁ ε _∙_ f

    empty-explore : Explore ℓ A
    empty-explore ε _ _ = ε

    point-explore : A → Explore ℓ A
    point-explore x _ _ f = f x

-- -}
-- -}
-- -}
-- -}
