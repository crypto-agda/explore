{-# OPTIONS --without-K #-}
open import Type
open import Data.Fin using (Fin; zero; suc; #_)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; refl)
open import HoTT
open Equivalences

open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
open import Explore.Universe

module Explore.Dice where

data Dice : ★₀ where
  ⚀ ⚁ ⚂ ⚃ ⚄ ⚅ : Dice

module ByHand where
    exploreDice : ∀ {m} → Explore m Dice
    exploreDice ε _∙_ f = f ⚀ ∙ (f ⚁ ∙ (f ⚂ ∙ (f ⚃ ∙ (f ⚄ ∙ f ⚅))))

    exploreDice-ind : ∀ {m p} → ExploreInd p (exploreDice {m})
    exploreDice-ind P ε _∙_ f = f ⚀ ∙ (f ⚁ ∙ (f ⚂ ∙ (f ⚃ ∙ (f ⚄ ∙ f ⚅))))

    open Explorable₀ exploreDice-ind public using () renaming (sum     to sumDice; product to productDice)

    module _ {ℓ} where
        open Explorableₛ  {ℓ} exploreDice-ind public using () renaming (reify   to reifyDice)
        open Explorableₛₛ {ℓ} exploreDice-ind public using () renaming (unfocus to unfocusDice)

Dice↔Fin6 : Dice ≃ Fin 6
Dice↔Fin6 = equiv (⇒) (⇐) ⇒⇐ ⇐⇒
  module Dice↔Fin6 where
    S = Dice
    T = Fin 6
    ⇒ : S → T
    ⇒ ⚀ = # 0
    ⇒ ⚁ = # 1
    ⇒ ⚂ = # 2
    ⇒ ⚃ = # 3
    ⇒ ⚄ = # 4
    ⇒ ⚅ = # 5
    ⇐ : T → S
    ⇐ zero = ⚀
    ⇐ (suc zero) = ⚁
    ⇐ (suc (suc zero)) = ⚂
    ⇐ (suc (suc (suc zero))) = ⚃
    ⇐ (suc (suc (suc (suc zero)))) = ⚄
    ⇐ (suc (suc (suc (suc (suc zero))))) = ⚅
    ⇐ (suc (suc (suc (suc (suc (suc ()))))))
    ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
    ⇐⇒ ⚀ = refl
    ⇐⇒ ⚁ = refl
    ⇐⇒ ⚂ = refl
    ⇐⇒ ⚃ = refl
    ⇐⇒ ⚄ = refl
    ⇐⇒ ⚅ = refl
    ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
    ⇒⇐ zero = refl
    ⇒⇐ (suc zero) = refl
    ⇒⇐ (suc (suc zero)) = refl
    ⇒⇐ (suc (suc (suc zero))) = refl
    ⇒⇐ (suc (suc (suc (suc zero)))) = refl
    ⇒⇐ (suc (suc (suc (suc (suc zero))))) = refl
    ⇒⇐ (suc (suc (suc (suc (suc (suc ()))))))

-- By using FinU' instead of FinU one get a special case for Fin 1 thus avoiding
-- a final ε in the exploration function.
open Explore.Universe.Isomorphism (Finᵁ' 6) (Finᵁ'-Fin 6 ≃-∙ ≃-sym Dice↔Fin6)
  public
  renaming ( isoᵉ to Diceᵉ
           ; isoⁱ to Diceⁱ
           -- ; isoˡ to Diceˡ
           -- ; isoᶠ to Diceᶠ
           ; isoˢ to Diceˢ
           ; isoᵖ to Diceᵖ
           ; isoʳ to Diceʳ
           ; isoᵘ to Diceᵘ
           ; isoˢ-ok to Diceˢ-ok
           ; isoˢ-stableUnder to Diceˢ-stableUnder
           ; μiso to μDice
           )

module _ {m} where
  open ByHand
  _≡ᵉ_ : (e₀ e₁ : Explore m Dice) → ★_ _
  _≡ᵉ_ = _≡_

  same-as-by-hand : exploreDice ≡ᵉ Diceᵉ
  same-as-by-hand = refl
