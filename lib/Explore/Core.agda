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

module _ {a} where
    BigOp : ∀ {ℓ} → ★ ℓ → ★ a → ★ (a ⊔ ℓ)
    BigOp M A = (A → M) → M

    Explore : ∀ ℓ → ★_ a → ★ (a ⊔ ₛ ℓ)
    Explore ℓ A = ∀ {M : ★ ℓ} (ε : M) (_∙_ : M → M → M) → BigOp M A

    BigOpMon : ∀ {c ℓ} → Monoid c ℓ → ★ a → ★ _
    BigOpMon M A = BigOp (Monoid.Carrier M) A

    ExploreMon : ∀ c ℓ → ★ a → ★ _
    ExploreMon c ℓ A = (M : Monoid c ℓ) → BigOpMon M A

    Explore₀ : ★ a → ★(a ⊔ ₁)
    Explore₀ = Explore ₀

    Explore₁ : ★ a → ★(a ⊔ ₂)
    Explore₁ = Explore ₁

    Sum : ★ a → ★ a
    Sum = BigOp ℕ

    Product : ★ a → ★ a
    Product = BigOp ℕ

    Count : ★ a → ★ a
    Count A = (A → 𝟚) → ℕ

    Find? : ∀ {b} → ★ a → ★(ₛ b ⊔ a)
    Find? {b} A = ∀ {B : ★ b} → (A →? B) →? B

    FindKey : ★ a → ★ a
    FindKey A = (A → 𝟚) →? A

-- These three basic combinators are defined here
-- since they are used to define ExploreInd
    module _ {ℓ} {A : ★ a} where
        merge-explore : Explore ℓ A → Explore ℓ A → Explore ℓ A
        merge-explore e₀ e₁ ε _∙_ f = e₀ ε _∙_ f ∙ e₁ ε _∙_ f

        empty-explore : Explore ℓ A
        empty-explore ε _ _ = ε

        point-explore : A → Explore ℓ A
        point-explore x _ _ f = f x

[Explore] : ∀ {a aₚ} → ([★₀] [→] [★] (ₛ (a ⊔ aₚ))) (Explore a)
[Explore] {a} {aₚ} Aₚ = ∀⟨ Mₚ ∶ [★] (a ⊔ aₚ)⟩[→] Mₚ [→] [Op₂] {_} {aₚ} Mₚ [→] (Aₚ [→] Mₚ) [→] Mₚ

module _ {ℓ₁ ℓ₂} ℓᵣ {a₁ a₂ aᵣ} where
    ⟦Explore⟧ : (⟦★⟧ {a₁} {a₂} aᵣ ⟦→⟧ ⟦★⟧ (a₁ ⊔ a₂ ⊔ aᵣ ⊔ ₛ (ℓ₁ ⊔ ℓ₂ ⊔ ℓᵣ))) (Explore ℓ₁) (Explore ℓ₂)
    ⟦Explore⟧ Aᵣ = ∀⟨ Mᵣ ∶ ⟦★⟧ (ℓ₁ ⊔ ℓ₂ ⊔ ℓᵣ) ⟩⟦→⟧ Mᵣ ⟦→⟧ ⟦Op₂⟧ {_} {_} {ℓᵣ} Mᵣ ⟦→⟧ (Aᵣ ⟦→⟧ Mᵣ) ⟦→⟧ Mᵣ

⟦Explore⟧₀ : (⟦★₀⟧ ⟦→⟧ ⟦★₁⟧) (Explore _) (Explore _)
⟦Explore⟧₀ = ⟦Explore⟧ _

-- -}
-- -}
-- -}
-- -}
