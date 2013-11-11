{-# OPTIONS --without-K #-}
open import Data.Nat
open import Data.Two
open import Data.Fin.NP
open import Type
open import Function
open import Relation.Binary.PropositionalEquality.NP

open import Explore.Universe
open import Explore.Core
open import Explore.Zero
open import Explore.One
open import Explore.Two

-- Exploring Fin comes in two flavors Regular & Custom
-- We recommend Regular if you want to work for arbitrary values of n.
-- We recommend Custom if you want to work for particular values of n (2, 6...).
module Explore.Fin where

module Regular n where
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

module Custom where
  module _ n where
    open Explore.Universe.Isomorphism (FinU' n) (FinU'↔Fin n)
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

  Finᵉ0-𝟘ᵉ : (λ {M : ★₀} (ε : M) op f → Finᵉ 0 ε op (f ∘ Fin▹𝟘)) ≡ 𝟘ᵉ
  Finᵉ0-𝟘ᵉ = refl

  Finᵉ1-𝟙ᵉ : (λ {M : ★₀} (ε : M) op f → Finᵉ 1 ε op (f ∘ Fin▹𝟙)) ≡ 𝟙ᵉ
  Finᵉ1-𝟙ᵉ = refl

  Finᵉ2-𝟚ᵉ : (λ {M : ★₀} (ε : M) op f → Finᵉ 2 ε op (f ∘ Fin▹𝟚)) ≡ 𝟚ᵉ
  Finᵉ2-𝟚ᵉ = refl

private
  module ByHand {ℓ} where
    open Regular
    Finᵉ' : ∀ n → Explore ℓ (Fin n)
    Finᵉ' zero    z _⊕_ f = z
    Finᵉ' (suc n) z _⊕_ f = f zero ⊕ Finᵉ' n z _⊕_ (f ∘ suc)

    -- Finᵉ and Finᵉ' are extensionally equal.
    -- Moreover the simplicity of the proof shows that the two functions are computing
    -- in the same way.
    Finᵉ-Finᵉ' : ∀ n {M} (ε : M) (_⊕_ : M → M → M) (f : Fin n → M) → Finᵉ n ε _⊕_ f ≡ Finᵉ' n ε _⊕_ f
    Finᵉ-Finᵉ' zero    ε _⊕_ f = idp
    Finᵉ-Finᵉ' (suc n) ε _⊕_ f = ap (_⊕_ (f zero))
                                    (Finᵉ-Finᵉ' n ε _⊕_ (f ∘ suc))
