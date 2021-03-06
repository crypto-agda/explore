{-# OPTIONS --without-K #-}
module Explore.README where

-- The core types behind exploration functions
open import Explore.Core

-- The core properties behind exploration functions
open import Explore.Properties

-- Lifting the dependent axiom of choice to sums and products
open import Explore.BigDistr

-- Constructions on top of exploration functions
open import Explore.Explorable

-- Specific constructions on top of summation functions
open import Explore.Summable

-- Exploration of Cartesian products (and Σ-types)
open import Explore.Product

-- Exploration of disjoint sums
open import Explore.Sum

-- Exploration of base types 𝟘, 𝟙, 𝟚, Fin n
open import Explore.Zero
open import Explore.One
open import Explore.Two
open import Explore.Fin

-- A type universe of explorable types
open import Explore.Universe.Type
open import Explore.Universe.Base
open import Explore.Universe

-- Transporting explorations across isomorphisms
open import Explore.Isomorphism

-- From binary trees to explorations and back
open import Explore.BinTree

-- Exploration functions form a monad
open import Explore.Monad

-- Some high-level properties about group homomorphisms and
-- group isomorphisms.
-- For instance the indistinguisability (One-time-pad like) for groups
open import Explore.Group

-- In a (bit) guessing game,
open import Explore.GuessingGameFlipping

-- An example with a specific type: 6 sided dice
open import Explore.Dice

-- TODO unfinished
-- BROKEN open import Explore.Function.Fin
open import Explore.Subset
