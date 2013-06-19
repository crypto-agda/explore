module Explore.BinTree where

open import Data.Tree.Binary
open import Explore.Type

fromBinTree : ∀ {m A} → BinTree A → Explore m A
fromBinTree (leaf x)   _   f = f x
fromBinTree (fork ℓ r) _∙_ f = fromBinTree ℓ _∙_ f ∙ fromBinTree r _∙_ f

fromBinTree-ind : ∀ {m p A} (t : BinTree A) → ExploreInd p (fromBinTree {m} t)
fromBinTree-ind (leaf x)   P P∙ Pf = Pf x
fromBinTree-ind (fork ℓ r) P P∙ Pf = P∙ (fromBinTree-ind ℓ P P∙ Pf)
                                        (fromBinTree-ind r P P∙ Pf)
