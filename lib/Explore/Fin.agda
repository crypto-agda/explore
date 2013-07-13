{-# OPTIONS --without-K #-}
module Explore.Fin where

import Level as L
open import Type
open import Function
open import Algebra
open import Algebra.FunctionProperties.NP
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
open import Data.Product
open import Function.Related.TypeIsomorphisms.NP
open import Relation.Binary.NP

open import Explore.Type
open import Explore.Explorable
--open import Explore.Explorable.Maybe

module _ n where
  T = Fin (suc n)

  iso = Maybe^𝟙↔Fin1+ n

  module _ {ℓ} where
    FinSucᵉ : Explore ℓ T
    FinSucᵉ _∙_ f = f zero ∙ {!FinSucᵉ _∙_ (f ∘ suc)!}

{-
module _ {A : ★}(μA : Explorable A) where

  sA = explore μA

  extend : ∀ {n} → A → (Fin n → A) → Fin (suc n) → A
  extend x g zero    = x
  extend x g (suc i) = g i

  ¬Fin0 : Fin 0 → A
  ¬Fin0 ()

  -- There is one function Fin 0 → A (called abs) so this should be fine
  -- if not there is a version below that forces the domain to be non-empty
  sFun : ∀ n → Explore _ (Fin n → A)
  sFun zero    op f = f ¬Fin0
  sFun (suc n) op f = sA op (λ x → sFun n op (f ∘ extend x))

  ind : ∀ n → ExploreInd _ (sFun n)
  ind zero    P P∙ Pf = Pf _
  ind (suc n) P P∙ Pf =
    explore-ind μA (λ sa → P (λ op f → sa op (λ x → sFun n op (f ∘ extend x))))
      P∙
      (λ x → ind n (λ sf → P (λ op f → sf op (f ∘ extend x)))
        P∙ (Pf ∘ extend x))

  sumFun : ∀ n → Sum (Fin n → A)
  sumFun n = sFun n _+_

  postulate
    ade : ∀ n → AdequateSum (sumFun n)

  μFun : ∀ {n} → Explorable (Fin n → A)
  μFun = mk _ (ind _) (ade _)

{-
μFinSuc : ∀ n → Explorable (Fin (suc n))
μFinSuc n = mk _ (ind n) {!!}
  where ind : ∀ n → ExploreInd _ (exploreFinSuc n)
        ind zero    P P∙ Pf = Pf zero
        ind (suc n) P P∙ Pf = P∙ (Pf zero) (ind n (λ s → P (λ op f → s op (f ∘ suc))) P∙ (Pf ∘ suc))
-}

postulate μFinSUI : ∀ {n} → SumStableUnderInjection (sum (μFinSuc n))

module BigDistr
  {A : ★}(μA : Explorable A)
  (cm       : CommutativeMonoid L.zero L.zero)
  -- we want (open CMon cm) !!!
  (_◎_      : let open CMon cm in C → C → C)
  (distrib  : let open CMon cm in _DistributesOver_ _≈_ _◎_ _∙_)
  (_◎-cong_ : let open CMon cm in _◎_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_) where

  open CMon cm

  μF→A = μFun μA

  -- Sum over A
  Σᴬ = explore μA _∙_

  -- Sum over (Fin(1+I)→A) functions
  Σ' : ∀ {I} → ((Fin (suc I) → A) → C) → C
  Σ' = explore μF→A _∙_

  -- Product over Fin(1+I) values
  Π' = λ I → explore (μFinSuc I) _◎_

  bigDistr : ∀ I F → Π' I (Σᴬ ∘ F) ≈ Σ' (Π' I ∘ _ˢ_ F)
  bigDistr zero    _ = refl
  bigDistr (suc I) F
    = Σᴬ (F zero) ◎ Π' I (Σᴬ ∘ F ∘ suc)
    ≈⟨ refl ◎-cong bigDistr I (F ∘ suc) ⟩
      Σᴬ (F zero) ◎ Σ' (Π' I ∘ _ˢ_ (F ∘ suc))
    ≈⟨ sym (explore-linʳ μA monoid _◎_ (F zero) (Σ' (Π' I ∘ _ˢ_ (F ∘ suc))) (proj₂ distrib)) ⟩
      Σᴬ (λ j → F zero j ◎ Σ' (Π' I ∘ _ˢ_ (F ∘ suc)))
    ≈⟨ explore-sg-ext μA semigroup (λ j → sym (explore-linˡ μF→A monoid _◎_ (Π' I ∘ _ˢ_ (F ∘ suc)) (F zero j) (proj₁ distrib))) ⟩
      (Σᴬ λ j → Σ' λ f → F zero j ◎ Π' I ((F ∘ suc) ˢ f))
    ∎

FinDist : ∀ {n} → DistFun (μFinSuc n) (λ μX → μFun μX)
FinDist μB c ◎ distrib ◎-cong f = BigDistr.bigDistr μB c ◎ distrib ◎-cong _ f
-- -}
