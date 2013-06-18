open import Function.Related.TypeIsomorphisms.NP
open import Function.Inverse.NP
open import Data.Maybe.NP
open import Data.Nat

open import Explore.Type
open import Explore.Explorable
open import Explore.Explorable.Sum

module Explore.Explorable.Maybe where

μMaybe : ∀ {A} → Explorable A → Explorable (Maybe A)
μMaybe μA = μ-iso (sym Maybe↔⊤⊎) (μ⊤ ⊎-μ μA)

μMaybe^ : ∀ {A} n → Explorable A → Explorable (Maybe^ n A)
μMaybe^ zero    μA = μA
μMaybe^ (suc n) μA = μMaybe (μMaybe^ n μA)
