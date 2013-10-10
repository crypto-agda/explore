open import Type
open import Level.NP
open import Data.Two
open import Function
open import Data.Product
open import Data.Sum
open import Data.Fin
open import Explore.Sum
open import Explore.Type
open import Explore.One
open import Explore.Explorable
open import Relation.Binary.PropositionalEquality using (refl)
import Function.Inverse.NP as FI
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP
open import Relation.Binary.Sum

module Explore.Two where

module _ {ℓ} where
    𝟚ᵉ : Explore ℓ 𝟚
    𝟚ᵉ _ _∙_ f = f 0₂ ∙ f 1₂

    𝟚ⁱ : ∀ {p} → ExploreInd p 𝟚ᵉ
    𝟚ⁱ _ _ _P∙_ Pf = Pf 0₂ P∙ Pf 1₂

open Explorable₀  𝟚ⁱ public using () renaming (sum     to 𝟚ˢ)
open Explorable₁₀ 𝟚ⁱ public using () renaming (reify   to 𝟚ʳ)
open Explorable₁₁ 𝟚ⁱ public using () renaming (unfocus to 𝟚ᵘ)

module _ {ℓ} where
    𝟚ˡ : Lookup {ℓ} 𝟚ᵉ
    𝟚ˡ = proj

    𝟚ᶠ : Focus {ℓ} 𝟚ᵉ
    𝟚ᶠ (0₂ , x) = inj₁ x
    𝟚ᶠ (1₂ , x) = inj₂ x

focused𝟚 : Focused {₀} 𝟚ᵉ
focused𝟚 = inverses 𝟚ᶠ 𝟚ᵘ (⇒) (⇐)
  where ⇒ : (x : Σ _ _) → _
        ⇒ (0₂ , x) = refl
        ⇒ (1₂ , x) = refl
        ⇐ : (x : _ ⊎ _) → _
        ⇐ (inj₁ x) = refl
        ⇐ (inj₂ x) = refl

𝟚ˢ-ok : AdequateSum 𝟚ˢ
𝟚ˢ-ok f = FI.sym (Fin-⊎-+ (f 0₂) (f 1₂) FI.∘ Σ𝟚↔⊎ (Fin ∘ f))

explore𝟚     = 𝟚ᵉ
explore𝟚-ind = 𝟚ⁱ
lookup𝟚      = 𝟚ˡ
reify𝟚       = 𝟚ʳ
focus𝟚       = 𝟚ᶠ
unfocus𝟚     = 𝟚ᵘ
sum𝟚         = 𝟚ˢ

-- DEPRECATED
μ𝟚 : Explorable 𝟚
μ𝟚 = mk _ 𝟚ⁱ 𝟚ˢ-ok
