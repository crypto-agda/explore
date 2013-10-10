{-# OPTIONS --without-K #-}
module Explore.BinTree where

open import Data.Tree.Binary
open import Explore.Type

fromBinTree : ∀ {m A} → BinTree A → Explore m A
fromBinTree (leaf x)   _ _   f = f x
fromBinTree (fork ℓ r) ε _∙_ f = fromBinTree ℓ ε _∙_ f ∙ fromBinTree r ε _∙_ f

fromBinTree-ind : ∀ {m p A} (t : BinTree A) → ExploreInd p (fromBinTree {m} t)
fromBinTree-ind (leaf x)   P _  P∙ Pf = Pf x
fromBinTree-ind (fork ℓ r) P Pε P∙ Pf = P∙ (fromBinTree-ind ℓ P Pε P∙ Pf)
                                           (fromBinTree-ind r P Pε P∙ Pf)
