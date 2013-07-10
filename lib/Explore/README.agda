{-# OPTIONS --without-K #-}
module Explore.README where

-- The core types behind exploration functions
open import Explore.Type

-- Constructions on top of exploration functions
open import Explore.Explorable

-- Specific constructions on top of summation functions
open import Explore.Summable

-- Exploration of Cartesian products (and Σ-types)
open import Explore.Product

-- Exploration of disjoint sums
open import Explore.Sum

-- From binary trees to explorations and back
open import Explore.BinTree

-- Exploration functions form a monad
open import Explore.Monad

-- Indistinguisability (One-time-pad like) for groups
open import Explore.GroupHomomorphism
