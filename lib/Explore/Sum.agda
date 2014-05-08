{-# OPTIONS --without-K #-}
{-

  The main definitions of this module are:

    * explore⊎
    * explore⊎-ind
    * adequate-sum⊎

-}
open import Type hiding (★)
open import Function.NP
open import Function.Extensionality
open import Data.Nat using (_+_)
open import Level.NP
open import Type.Identities
open import Data.Product.NP
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_])
open import Data.Sum.Logical
open import HoTT
open import Data.Fin using (Fin)
open import Relation.Binary.Logical
open import Relation.Binary.Sum
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_ ; module ≡-Reasoning; cong; !_; _∙_; refl; ap)

open import Explore.Core
open import Explore.Properties
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
      ⊎ᶜ = e₁ (f ∘ inl) ∙ e₂ (f ∘ inr)

module _ {m A B} where
    explore⊎ : Explore m A → Explore m B → Explore m (A ⊎ B)
    explore⊎ exploreᴬ exploreᴮ ε _∙_ = ⊎ᶜ _∙_ (exploreᴬ ε _∙_) (exploreᴮ ε _∙_)

    module _ {p} {eᴬ : Explore m A} {eᴮ : Explore m B} where
        explore⊎-ind : ExploreInd p eᴬ → ExploreInd p eᴮ → ExploreInd p (explore⊎ eᴬ eᴮ)
        explore⊎-ind Psᴬ Psᴮ P Pε P∙ Pf
        -- TODO clean this up:
          = P∙ (Psᴬ (λ s → P (λ _ _ f → s _ _ (f ∘ inl))) Pε P∙ (Pf ∘ inl))
               (Psᴮ (λ s → P (λ _ _ f → s _ _ (f ∘ inr))) Pε P∙ (Pf ∘ inr))

module _ {ℓ₀ ℓ₁ ℓᵣ}
         {A₀ A₁} {Aᵣ : ⟦★₀⟧ A₀ A₁}
         {B₀ B₁} {Bᵣ : ⟦★₀⟧ B₀ B₁}
         {eᴬ₀ : Explore ℓ₀ A₀} {eᴬ₁ : Explore ℓ₁ A₁}(eᴬᵣ : ⟦Explore⟧ᵤ ℓ₀ ℓ₁ ℓᵣ Aᵣ eᴬ₀ eᴬ₁)
         {eᴮ₀ : Explore ℓ₀ B₀} {eᴮ₁ : Explore ℓ₁ B₁}(eᴮᵣ : ⟦Explore⟧ᵤ ℓ₀ ℓ₁ ℓᵣ Bᵣ eᴮ₀ eᴮ₁)
         where
    ⟦explore⊎⟧ : ⟦Explore⟧ᵤ _ _ ℓᵣ (Aᵣ ⟦⊎⟧ Bᵣ) (explore⊎ eᴬ₀ eᴮ₀) (explore⊎ eᴬ₁ eᴮ₁)
    ⟦explore⊎⟧ P Pε P∙ Pf
       = P∙ (eᴬᵣ P Pε P∙ (Pf ∘ ⟦inl⟧))
            (eᴮᵣ P Pε P∙ (Pf ∘ ⟦inr⟧))

infixr 4 _⊎ᵉ_ _⊎ⁱ_ _⊎ˢ_
_⊎ᵉ_ = explore⊎
_⊎ⁱ_ = explore⊎-ind

_⊎ˢ_ : ∀ {A B} → Sum A → Sum B → Sum (A ⊎ B)
_⊎ˢ_ = ⊎ᶜ _+_

module _ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B}{{_ : UA}} where

    adequate-sum⊎ : Adequate-sum sumᴬ → Adequate-sum sumᴮ → Adequate-sum (sumᴬ ⊎ˢ sumᴮ)
    adequate-sum⊎ asumᴬ asumᴮ f    = (Fin (sumᴬ (f ∘ inl) + sumᴮ (f ∘ inr)))
                                   ≡⟨ ! Fin-⊎-+ ⟩
                                     (Fin (sumᴬ (f ∘ inl)) ⊎ Fin (sumᴮ (f ∘ inr)))
                                   ≡⟨ ⊎= (asumᴬ (f ∘ inl)) (asumᴮ (f ∘ inr)) ⟩
                                     (Σ A (Fin ∘ f ∘ inl) ⊎ Σ B (Fin ∘ f ∘ inr))
                                   ≡⟨ ! dist-⊎-Σ ⟩
                                     Σ (A ⊎ B) (Fin ∘ f)
                                   ∎
      where open ≡-Reasoning

    _⊎ᵃ_ = adequate-sum⊎

module _ {ℓ} {A B} {eᴬ : Explore (ₛ ℓ) A} {eᴮ : Explore (ₛ ℓ) B} where
  eᴬ⁺ᴮ = eᴬ ⊎ᵉ eᴮ
  focus⊎ : Focus eᴬ → Focus eᴮ → Focus eᴬ⁺ᴮ
  focus⊎ fᴬ fᴮ (inl x , y) = inl (fᴬ (x , y))
  focus⊎ fᴬ fᴮ (inr x , y) = inr (fᴮ (x , y))

  unfocus⊎ : Unfocus eᴬ → Unfocus eᴮ → Unfocus eᴬ⁺ᴮ
  unfocus⊎ fᴬ fᴮ (inl x) = first inl (fᴬ x)
  unfocus⊎ fᴬ fᴮ (inr y) = first inr (fᴮ y)

  Σᵉ⊎-ok : {{_ : UA}} → Adequate-Σᵉ eᴬ → Adequate-Σᵉ eᴮ → Adequate-Σᵉ eᴬ⁺ᴮ
  Σᵉ⊎-ok fᴬ fᴮ _ = ⊎= (fᴬ _) (fᴮ _) ∙ ! dist-⊎-Σ

  lookup⊎ : Lookup eᴬ → Lookup eᴮ → Lookup (eᴬ ⊎ᵉ eᴮ)
  lookup⊎ lookupᴬ lookupᴮ (x , y) = [inl: lookupᴬ x ,inr: lookupᴮ y ]

  reify⊎ : Reify eᴬ → Reify eᴮ → Reify (eᴬ ⊎ᵉ eᴮ)
  reify⊎ reifyᴬ reifyᴮ f = (reifyᴬ (f ∘ inl)) , (reifyᴮ (f ∘ inr))

  Πᵉ⊎-ok : {{_ : UA}}{{_ : FunExt}} → Adequate-Πᵉ eᴬ → Adequate-Πᵉ eᴮ → Adequate-Πᵉ eᴬ⁺ᴮ
  Πᵉ⊎-ok fᴬ fᴮ _ = ×= (fᴬ _) (fᴮ _) ∙ ! dist-×-Π

-- DEPRECATED
open ExplorableRecord
_⊎-μ_ : ∀ {{_ : UA}} {A B} → Explorable A → Explorable B → Explorable (A ⊎ B)
μA ⊎-μ μB = mk _ (explore-ind μA ⊎ⁱ explore-ind μB)
                 (adequate-sum⊎ (adequate-sum μA) (adequate-sum μB))

 -- -}
 -- -}
 -- -}
