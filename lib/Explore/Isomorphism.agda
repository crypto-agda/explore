{-# OPTIONS --without-K #-}
open import Level.NP
open import Type hiding (★)
open import Type.Identities
open import Function.NP
open import Function.Extensionality
open import Data.Product
open import Data.Sum
open import Relation.Binary.Logical
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Binary.NP
open import HoTT
open Equivalences

open import Explore.Core
open import Explore.Properties
open import Explore.Explorable
import Explore.Monad

-- NOTE: it would be nice to have another module to change the definition of an exploration
-- function by an extensionally equivalent one. Combined with this module one could both
-- pick the reduction behavior we want and save some proof effort.
module Explore.Isomorphism
  {-a-} {A B : ★₀ {-a-}} (e : A ≃ B) where
a = ₀

private
  module M {ℓ} = Explore.Monad {a} ℓ
  e⁻ = ≃-sym e
  module E = Equiv e
  e→ = E.·→

module _ {ℓ} (Aᵉ : Explore ℓ A) where
  explore-iso : Explore ℓ B
  explore-iso = M.map e→ Aᵉ

private
  Bᵉ = explore-iso

module _ {ℓ p} {Aᵉ : Explore ℓ A} (Aⁱ : ExploreInd p Aᵉ) where
  explore-iso-ind : ExploreInd p (Bᵉ Aᵉ)
  explore-iso-ind = M.map-ind e→ Aⁱ

private
  Bⁱ = explore-iso-ind

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aˡ : Lookup {ℓ} Aᵉ) where
  lookup-iso : Lookup {ℓ} (Bᵉ Aᵉ)
  lookup-iso {C} d b = tr C (E.·←-inv-r b) (Aˡ d (E.·← b))

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (Aᶠ : Focus {ℓ} Aᵉ) where
  focus-iso : Focus {ℓ} (Bᵉ Aᵉ)
  focus-iso {C} (b , c) = Aᶠ (E.·← b , c')
    where c' = tr C (! (E.·←-inv-r b)) c

module _ (Aˢ : Sum A) where
  sum-iso : Sum B
  sum-iso h = Aˢ (h ∘ e→)

module _ (Aᵖ : Product A) where
  product-iso : Product B
  product-iso h = Aᵖ (h ∘ e→)

module FromExplore-iso
         (Aᵉ : ∀ {ℓ} → Explore ℓ A)
       = FromExplore (Bᵉ Aᵉ)

module FromExploreInd-iso
         {Aᵉ : ∀ {ℓ} → Explore ℓ A}
         (Aⁱ : ∀ {ℓ p} → ExploreInd {ℓ} p Aᵉ)
       = FromExploreInd (Bⁱ Aⁱ)

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (ΣAᵉ-ok : Adequate-Σ (Σᵉ Aᵉ)) {{_ : UA}} {{_ : FunExt}} where
  Σ-iso-ok : Adequate-Σ (Σᵉ (Bᵉ Aᵉ))
  Σ-iso-ok F = ΣAᵉ-ok (F ∘ e→) ∙ Σ-fst≃ e _

module _ {ℓ} {Aᵉ : Explore (ₛ ℓ) A} (ΠAᵉ-ok : Adequate-Π (Πᵉ Aᵉ)) {{_ : UA}} {{_ : FunExt}} where
  Π-iso-ok : Adequate-Π (Πᵉ (Bᵉ Aᵉ))
  Π-iso-ok F = ΠAᵉ-ok (F ∘ e→) ∙ Π-dom≃ e _

open Adequacy _≡_
module _ {Aˢ : Sum A} (Aˢ-ok : Adequate-sum Aˢ) {{_ : UA}} {{_ : FunExt}} where
  sum-iso-ok : Adequate-sum (sum-iso Aˢ)
  sum-iso-ok h = Aˢ-ok (h ∘ e→) ∙ Σ-fst≃ e _

module _ {Aᵖ : Product A} (Aᵖ-ok : Adequate-product Aᵖ) {{_ : UA}} {{_ : FunExt}} where
  product-iso-ok : Adequate-product (product-iso Aᵖ)
  product-iso-ok g = Aᵖ-ok (g ∘ e→) ∙ Π-dom≃ e _

module _
    {ℓ₀ ℓ₁ ℓᵣ}
    {aᵣ} {Aᵣ : ⟦★⟧ aᵣ A A}
    {bᵣ} {Bᵣ : ⟦★⟧ bᵣ B B}
    (e→ᵣ : (Aᵣ ⟦→⟧ Bᵣ) e→ e→)
    {expᴬ₀ : Explore ℓ₀ A} {expᴬ₁ : Explore ℓ₁ A}(expᴬᵣ : ⟦Explore⟧ ℓᵣ Aᵣ expᴬ₀ expᴬ₁) where
  ⟦explore-iso⟧ : ⟦Explore⟧ ℓᵣ Bᵣ (explore-iso expᴬ₀) (explore-iso expᴬ₁)
  ⟦explore-iso⟧ P Pε P⊕ Pf = expᴬᵣ P Pε P⊕ (Pf ∘ e→ᵣ)

-- -}
-- -}
-- -}
