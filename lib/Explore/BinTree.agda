{-# OPTIONS --without-K #-}
module Explore.BinTree where

open import Data.Tree.Binary

open import Explore.Core
open import Explore.Properties

fromBinTree : ∀ {m} {A} → BinTree A → Explore m A
fromBinTree empty      = empty-explore
fromBinTree (leaf x)   = point-explore x
fromBinTree (fork ℓ r) = merge-explore (fromBinTree ℓ) (fromBinTree r)

fromBinTree-ind : ∀ {m p A} (t : BinTree A) → ExploreInd p (fromBinTree {m} t)
fromBinTree-ind empty      = empty-explore-ind
fromBinTree-ind (leaf x)   = point-explore-ind x
fromBinTree-ind (fork ℓ r) = merge-explore-ind (fromBinTree-ind ℓ)
                                               (fromBinTree-ind r)
{-
fromBinTree : ∀ {m A} → BinTree A → Explore m A
fromBinTree (leaf x)   _ _   f = f x
fromBinTree (fork ℓ r) ε _∙_ f = fromBinTree ℓ ε _∙_ f ∙ fromBinTree r ε _∙_ f

fromBinTree-ind : ∀ {m p A} (t : BinTree A) → ExploreInd p (fromBinTree {m} t)
fromBinTree-ind (leaf x)   P _  P∙ Pf = Pf x
fromBinTree-ind (fork ℓ r) P Pε P∙ Pf = P∙ (fromBinTree-ind ℓ P Pε P∙ Pf)
                                           (fromBinTree-ind r P Pε P∙ Pf)
-}
