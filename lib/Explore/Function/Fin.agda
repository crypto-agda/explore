{-# OPTIONS --without-K #-}
open import Type
open import Function
open import Function.Extensionality
open import Data.Fin using (Fin)
open import Level.NP
open import Algebra
open import Algebra.FunctionProperties.NP
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
open import Data.Product
open import Relation.Binary.NP

open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
import Explore.Fin
open Explore.Fin.Regular
open import HoTT

module Explore.Function.Fin where

postulate
  Postulate-FinFunˢ-ok : ★
open ExplorableRecord

module _ {A : ★}(μA : Explorable A) where

  eᴬ = explore μA

  extend : ∀ {n} → A → (Fin n → A) → Fin (suc n) → A
  extend x g zero    = x
  extend x g (suc i) = g i

  ¬Fin0 : Fin 0 → A
  ¬Fin0 ()

  -- There is one function Fin 0 → A (called abs) so this should be fine
  -- if not there is a version below that forces the domain to be non-empty
  FinFunᵉ : ∀ n → Explore _ (Fin n → A)
  FinFunᵉ zero    z op f = f ¬Fin0
  FinFunᵉ (suc n) z op f = eᴬ z op (λ x → FinFunᵉ n z op (f ∘ extend x))

  FinFunⁱ : ∀ n → ExploreInd _ (FinFunᵉ n)
  FinFunⁱ zero    P Pz P∙ Pf = Pf _
  FinFunⁱ (suc n) P Pz P∙ Pf =
    explore-ind μA (λ sa → P (λ z op f → sa z op (λ x → FinFunᵉ n z op (f ∘ extend x))))
      Pz P∙
      (λ x → FinFunⁱ n (λ sf → P (λ z op f → sf z op (f ∘ extend x)))
        Pz P∙ (Pf ∘ extend x))

  FinFunˢ : ∀ n → Sum (Fin n → A)
  FinFunˢ n = FinFunᵉ n 0 _+_

  postulate
    FinFunˢ-ok : ∀ {{_ : Postulate-FinFunˢ-ok}} n → Adequate-sum (FinFunˢ n)

  μFinFun : ∀ {{_ : Postulate-FinFunˢ-ok}} {n} → Explorable (Fin n → A)
  μFinFun = mk _ (FinFunⁱ _) (FinFunˢ-ok _)

module BigDistr
  {{_ : Postulate-FinFunˢ-ok}} {{_ : FunExt}} {{_ : UA}}
  {A : ★}(μA : Explorable A)
  (cm           : CommutativeMonoid ₀ ₀)
  -- we want (open CMon cm) !!!
  (_◎_          : let open CMon cm in C → C → C)
  (ε-◎          : let open CMon cm in Zero _≈_ ε _◎_)
  (distrib      : let open CMon cm in _DistributesOver_ _≈_ _◎_ _∙_)
  (_◎-cong_     : let open CMon cm in _◎_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_) where

  open CMon cm renaming (sym to ≈-sym)

  μF→A = μFinFun μA

  -- Sum over A
  Σᴬ = explore μA ε _∙_

  -- Sum over (Fin(1+I)→A) functions
  Σ' : ∀ {I} → ((Fin I → A) → C) → C
  Σ' = explore μF→A ε _∙_

  -- Product over Fin(1+I) values
  Π' = λ I → explore (μFin I) ε _◎_

  bigDistr : ∀ I F → Π' I (Σᴬ ∘ F) ≈ Σ' (Π' I ∘ _ˢ_ F)
  bigDistr zero    _ = refl
  bigDistr (suc I) F
    = Σᴬ (F zero) ◎ Π' I (Σᴬ ∘ F ∘ suc)
    ≈⟨ refl ◎-cong bigDistr I (F ∘ suc) ⟩
      Σᴬ (F zero) ◎ Σ' (Π' I ∘ _ˢ_ (F ∘ suc))
    ≈⟨ ≈-sym (explore-linʳ μA monoid _◎_ (F zero) (Σ' (Π' I ∘ _ˢ_ (F ∘ suc))) (proj₁ ε-◎ _) (proj₂ distrib)) ⟩
      Σᴬ (λ j → F zero j ◎ Σ' (Π' I ∘ _ˢ_ (F ∘ suc)))
    ≈⟨ explore-mon-ext μA monoid (λ j → ≈-sym (explore-linˡ μF→A monoid _◎_ (Π' I ∘ _ˢ_ (F ∘ suc)) (F zero j) (proj₂ ε-◎ _) (proj₁ distrib))) ⟩
      (Σᴬ λ j → Σ' λ f → F zero j ◎ Π' I ((F ∘ suc) ˢ f))
    ∎

module _
  {{_ : Postulate-FinFunˢ-ok}}{{_ : UA}}{{_ : FunExt}} where

  FinDist : ∀ {n} → DistFun (μFin n) (λ μX → μFinFun μX)
  FinDist μB c ◎ distrib ◎-cong f = BigDistr.bigDistr μB c ◎ distrib ◎-cong f _
