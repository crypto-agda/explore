{-# OPTIONS --without-K #-}
{-

  The main definitions of this module are:

    * explore⊎
    * explore⊎-ind
    * adequate-sum⊎

-}
open import Type hiding (★)
open import Function.NP
open import Data.Nat using (_+_)
open import Level.NP
import Function.Inverse.NP as FI
import Function.Related as FR
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP
open import Data.Product.NP
open import Data.Sum
open import Data.Bit
open import Data.Fin using (Fin)
open import Relation.Binary.Sum
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_ ; module ≡-Reasoning; cong)

open import Explore.Type
open import Explore.Explorable

module Explore.Sum where

module _ {a b u} {A : ★ a} {B : ★ b} {U : ★ u}
         (_∙_ : U → U → U)
         (e₁  : (A → U) → U)
         (e₂  : (B → U) → U)
         (f   : (A ⊎ B) → U)
  where
      -- find a better place/name for it
      ⊎ᶜ : U
      ⊎ᶜ = e₁ (f ∘ inj₁) ∙ e₂ (f ∘ inj₂)

module _ {m A B} where
    explore⊎ : Explore m A → Explore m B → Explore m (A ⊎ B)
    explore⊎ exploreᴬ exploreᴮ _∙_ = ⊎ᶜ _∙_ (exploreᴬ _∙_) (exploreᴮ _∙_)

    module _ {p} {sᴬ : Explore m A} {sᴮ : Explore m B} where
        explore⊎-ind : ExploreInd p sᴬ → ExploreInd p sᴮ → ExploreInd p (explore⊎ sᴬ sᴮ)
        explore⊎-ind Psᴬ Psᴮ P P∙ Pf
        -- TODO clean this up:
          = P∙ (Psᴬ (λ s → P (λ _ f → s _ (f ∘ inj₁))) P∙ (Pf ∘ inj₁))
               (Psᴮ (λ s → P (λ _ f → s _ (f ∘ inj₂))) P∙ (Pf ∘ inj₂))

infixr 4 _⊎ᵉ_ _⊎ⁱ_ _⊎ˢ_
_⊎ᵉ_ = explore⊎
_⊎ⁱ_ = explore⊎-ind

_⊎ˢ_ : ∀ {A B} → Sum A → Sum B → Sum (A ⊎ B)
_⊎ˢ_ = ⊎ᶜ _+_

module _ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B} where

    adequate-sum⊎ : AdequateSum sumᴬ → AdequateSum sumᴮ → AdequateSum (sumᴬ ⊎ˢ sumᴮ)
    adequate-sum⊎ asumᴬ asumᴮ f    = (Fin (sumᴬ (f ∘ inj₁) + sumᴮ (f ∘ inj₂)))
                                   ↔⟨ FI.sym (Fin-⊎-+ _ _) ⟩
                                     (Fin (sumᴬ (f ∘ inj₁)) ⊎ Fin (sumᴮ (f ∘ inj₂)))
                                   ↔⟨ asumᴬ (f ∘ inj₁) ⊎-cong asumᴮ (f ∘ inj₂) ⟩
                                     (Σ A (Fin ∘ f ∘ inj₁) ⊎ Σ B (Fin ∘ f ∘ inj₂))
                                   ↔⟨ FI.sym Σ⊎-distrib ⟩
                                     Σ (A ⊎ B) (Fin ∘ f)
                                   ∎
      where open FR.EquationalReasoning

    _⊎ᵃ_ = adequate-sum⊎

module _ {ℓ} {A B} {sᴬ : Explore (ₛ ℓ) A} {sᴮ : Explore (ₛ ℓ) B} where
  sᴬ⁺ᴮ = sᴬ ⊎ᵉ sᴮ
  focus⊎ : Focus sᴬ → Focus sᴮ → Focus sᴬ⁺ᴮ
  focus⊎ fᴬ fᴮ (inj₁ x , y) = inj₁ (fᴬ (x , y))
  focus⊎ fᴬ fᴮ (inj₂ x , y) = inj₂ (fᴮ (x , y))

  unfocus⊎ : Unfocus sᴬ → Unfocus sᴮ → Unfocus sᴬ⁺ᴮ
  unfocus⊎ fᴬ fᴮ (inj₁ x) = first inj₁ (fᴬ x)
  unfocus⊎ fᴬ fᴮ (inj₂ y) = first inj₂ (fᴮ y)

  {-
  _⊎-focused_ : Focused sᴬ → Focused sᴮ → Focused {L.zero} sᴬ⁺ᴮ
  _⊎-focused_ fᴬ fᴮ {B} = inverses (to fᴬ ⊎-focus to fᴮ) (from fᴬ ⊎-unfocus from fᴮ) (⇒) (⇐)
      where
        ⇒ : (x : Σ (A ⊎ {!!}) {!!}) → _
        ⇒ (x , y) = {!!}
        ⇐ : (x : sᴬ _⊎_ (B ∘ inj₁) ⊎ sᴮ _⊎_ (B ∘ inj₂)) → _
        ⇐ (inj₁ x) = cong inj₁ {!!}
        ⇐ (inj₂ x) = cong inj₂ {!!}
  -}

  lookup⊎ : Lookup sᴬ → Lookup sᴮ → Lookup (sᴬ ⊎ᵉ sᴮ)
  lookup⊎ lookupᴬ lookupᴮ (x , y) = [ lookupᴬ x , lookupᴮ y ]

  reify⊎ : Reify sᴬ → Reify sᴮ → Reify (sᴬ ⊎ᵉ sᴮ)
  reify⊎ reifyᴬ reifyᴮ f = (reifyᴬ (f ∘ inj₁)) , (reifyᴮ (f ∘ inj₂))

-- DEPRECATED
_⊎-μ_ : ∀ {A B} → Explorable A → Explorable B → Explorable (A ⊎ B)
μA ⊎-μ μB = mk _ (explore-ind μA ⊎ⁱ explore-ind μB)
                 (adequate-sum⊎ (adequate-sum μA) (adequate-sum μB))

 -- -}
 -- -}
 -- -}
