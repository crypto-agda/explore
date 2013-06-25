module Explore.Explorable.Isos where

open import Function
open import Data.Product
open import Data.Nat
open import Data.Vec renaming (sum to vsum)
open import Function.Related.TypeIsomorphisms.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_)

open import Explore.Type
open import Explore.Explorable
open import Explore.Product

swap-μ : ∀ {A B} → Explorable (A × B) → Explorable (B × A)
swap-μ = μ-iso swap-iso

swapS-preserve : ∀ {A B} f (μA×B : Explorable (A × B)) → sum μA×B f ≡ sum (swap-μ μA×B) (f ∘ swap)
swapS-preserve = μ-iso-preserve swap-iso

μ^ : ∀ {A} (μA : Explorable A) n → Explorable (A ^ n)
μ^ μA zero    = μLift μ⊤
μ^ μA (suc n) = μA ×-μ μ^ μA n

μVec : ∀ {A} (μA : Explorable A) n  → Explorable (Vec A n)
μVec μA n = μ-iso (^↔Vec n) (μ^ μA n)
