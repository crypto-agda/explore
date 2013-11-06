{-# OPTIONS --without-K #-}
open import Explore.Universe

module Explore.Fin n where

open Explore.Universe.Isomorphism (FinU n) (FinU↔Fin n)
  public
  renaming ( isoᵉ to Finᵉ
           ; isoⁱ to Finⁱ
           ; isoˡ to Finˡ
           ; isoᶠ to Finᶠ
           ; isoˢ to Finˢ
           ; isoᵖ to Finᵖ
           ; isoʳ to Finʳ
           ; isoᵘ to Finᵘ
           ; isoˢ-ok to Finˢ-ok
           ; isoˢ-stableUnder to Finˢ-stableUnder
           ; μiso to μFin
           )
