{-# OPTIONS --without-K #-}
open import Type
open import Function as F
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Explore.Type
open import Explore.Explorable
open import Explore.Fin
open import Level.NP
open import Explore.Monad ₀ renaming (map to map-explore)
import Function.Inverse.NP as FI
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP

module Explore.Dice {-{_ : Postulate-Finˢ-ok}-} where

data Dice : ★₀ where
  ⚀ ⚁ ⚂ ⚃ ⚄ ⚅ : Dice

exploreDice : ∀ {m} → Explore m Dice
exploreDice ε _∙_ f = f ⚀ ∙ (f ⚁ ∙ (f ⚂ ∙ (f ⚃ ∙ (f ⚄ ∙ f ⚅))))

exploreDice-ind : ∀ {m p} → ExploreInd p (exploreDice {m})
exploreDice-ind P ε _∙_ f = f ⚀ ∙ (f ⚁ ∙ (f ⚂ ∙ (f ⚃ ∙ (f ⚄ ∙ f ⚅))))

open Explorable₀  exploreDice-ind public using () renaming (sum     to sumDice; product to productDice)
open Explorable₁₀ exploreDice-ind public using () renaming (reify   to reifyDice)
open Explorable₁₁ exploreDice-ind public using () renaming (unfocus to unfocusDice)

Dice↔Fin6 : Dice ↔ Fin 6
Dice↔Fin6 = inverses (⇒) (⇐) ⇐⇒ ⇒⇐
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

    {-
-- This is unfinished it shows two ways:
-- 1) use the Fin 6 ↔ Dice iso
-- 2) do the adequacy directly
exploreDice-ok : AdequateSum sumDice
exploreDice-ok f = p FI.∘ {!Dice↔Fin6.!}
  where
    p : Fin (map-explore Dice↔Fin6.⇐ (explore (μFin 6)) 0 _+_ f) ↔ Σ Dice (Fin ∘ f)
    p = adequate-sum (μ-iso (FI.sym Dice↔Fin6) (μFin 6)) f

    direct = inverses (⇒) (⇐) ⇐⇒ ⇒⇐
    S = Fin (sumDice f)
    T = Σ Dice (Fin F.∘ f)
    ⇒ : S → T
    ⇒ x with sumDice f
    ⇒ (zero {n})   | .(suc n) = {!!}
    ⇒ (suc {n} x₁) | .(suc n) = {!!}
    ⇐ : T → S
    ⇐ (⚀ , x) = inject+ _ x
    ⇐ (⚁ , x) = raise (f ⚀) (inject+ _ x)
    ⇐ (⚂ , x) = raise (f ⚀) (raise (f ⚁) (inject+ _ x))
    ⇐ (⚃ , x) = raise (f ⚀) (raise (f ⚁) (raise (f ⚂) (inject+ _ x)))
    ⇐ (⚄ , x) = raise (f ⚀) (raise (f ⚁) (raise (f ⚂) (raise (f ⚃) (inject+ _ x))))
    ⇐ (⚅ , x) = raise (f ⚀) (raise (f ⚁) (raise (f ⚂) (raise (f ⚃) (raise (f ⚄) x))))
    ⇐⇒ : ∀ x → ⇐ (⇒ x) ≡ x
    ⇐⇒ x = {!!}
    ⇒⇐ : ∀ x → ⇒ (⇐ x) ≡ x
    ⇒⇐ (⚀ , x) = {!!}
    ⇒⇐ (⚁ , x) = {!!}
    ⇒⇐ (⚂ , x) = {!!}
    ⇒⇐ (⚃ , x) = {!!}
    ⇒⇐ (⚄ , x) = {!!}
    ⇒⇐ (⚅ , x) = {!!}

μDice : Explorable Dice
μDice = mk _ exploreDice-ind exploreDice-ok

-}
