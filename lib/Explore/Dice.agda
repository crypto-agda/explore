{-# OPTIONS --without-K #-}
open import Type
open import Data.Fin using (Fin; zero; suc; #_)
import Function.Inverse.NP as Inv
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open Inv using (_↔_)

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

    open Explorable₀  exploreDice-ind public using () renaming (sum     to sumDice; product to productDice)
    open Explorable₁₀ exploreDice-ind public using () renaming (reify   to reifyDice)
    open Explorable₁₁ exploreDice-ind public using () renaming (unfocus to unfocusDice)

Dice↔Fin6 : Dice ↔ Fin 6
Dice↔Fin6 = Inv.inverses (⇒) (⇐) ⇐⇒ ⇒⇐
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

open Explore.Universe.Isomorphism (FinU 6) (Inv.sym Dice↔Fin6 Inv.∘ FinU↔Fin 6)
  public
  renaming ( isoᵉ to Diceᵉ
           ; isoⁱ to Diceⁱ
           ; isoˡ to Diceˡ
           ; isoᶠ to Diceᶠ
           ; isoˢ to Diceˢ
           ; isoᵖ to Diceᵖ
           ; isoʳ to Diceʳ
           ; isoᵘ to Diceᵘ
           ; isoˢ-ok to Diceˢ-ok
           ; isoˢ-stableUnder to Diceˢ-stableUnder
           ; μiso to μDice
           )
