{-# OPTIONS --without-K #-}
module Explore.BinTree where

open import Level.NP
open import Type hiding (★)
open import Data.Tree.Binary
open import Data.Zero
open import Data.Product

open import Relation.Binary.PropositionalEquality.NP
open import HoTT
open Equivalences
open import Type.Identities
open import Function.Extensionality

open import Explore.Core
open import Explore.Properties
open import Explore.Zero
open import Explore.Sum
open import Explore.Isomorphism

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

AnyP≡ΣfromBinTree : ∀ {p}{A : ★ _}{P : A → ★ p}(xs : BinTree A) → Any P xs ≡ Σᵉ (fromBinTree xs) P
AnyP≡ΣfromBinTree empty    = idp
AnyP≡ΣfromBinTree (leaf x) = idp
AnyP≡ΣfromBinTree (fork xs xs₁) = ⊎= (AnyP≡ΣfromBinTree xs) (AnyP≡ΣfromBinTree xs₁)


module _ {{_ : UA}}{{_ : FunExt}}{A : ★ ₀} where


  exploreΣ∈ : ∀ {m} xs → Explore m (Σ A λ x → Any (_≡_ x) xs)
  exploreΣ∈ empty = explore-iso (coe-equiv (Lift≡id ∙ ! ×𝟘-snd  ∙ ×= idp (! Lift≡id))) Lift𝟘ᵉ
  exploreΣ∈ (leaf x) = point-explore (x , idp)
  exploreΣ∈ (fork xs xs₁) = explore-iso (coe-equiv (! Σ⊎-split)) (exploreΣ∈ xs ⊎ᵉ exploreΣ∈ xs₁)

  Σᵉ-adq-exploreΣ∈ : ∀ {m} xs → Adequate-Σᵉ {m} (exploreΣ∈ xs)
  Σᵉ-adq-exploreΣ∈ empty = Σ-iso-ok (coe-equiv (Lift≡id ∙ ! ×𝟘-snd ∙ ×= idp (! Lift≡id)))
    {Aᵉ = Lift𝟘ᵉ} ΣᵉLift𝟘-ok
  Σᵉ-adq-exploreΣ∈ (leaf x₁) F = ! Σ𝟙-snd ∙ Σ-fst≃ (≃-sym (Σx≡≃𝟙 x₁)) F
  Σᵉ-adq-exploreΣ∈ (fork xs xs₁) = Σ-iso-ok (coe-equiv (! Σ⊎-split)) {Aᵉ = exploreΣ∈ xs ⊎ᵉ exploreΣ∈ xs₁}
               (Σᵉ⊎-ok {eᴬ = exploreΣ∈ xs}{eᴮ = exploreΣ∈ xs₁} (Σᵉ-adq-exploreΣ∈ xs) (Σᵉ-adq-exploreΣ∈ xs₁))

module _ {{_ : UA}}{{_ : FunExt}}{A : ★ ₀}{P : A → ★ _}(explore-P : ∀ {m} x → Explore m (P x)) where
  open import Explore.Zero
  open import Explore.Sum
  open import Explore.Isomorphism

  exploreAny : ∀ {m} xs → Explore m (Any P xs)
  exploreAny empty         = Lift𝟘ᵉ
  exploreAny (leaf x)      = explore-P x
  exploreAny (fork xs xs₁) = exploreAny xs ⊎ᵉ exploreAny xs₁

  module _ (Σᵉ-adq-explore-P : ∀ {m} x → Adequate-Σᵉ {m} (explore-P x)) where
    Σᵉ-adq-exploreAny : ∀ {m} xs → Adequate-Σᵉ {m} (exploreAny xs)
    Σᵉ-adq-exploreAny empty F         = ! Σ𝟘-lift∘fst ∙ Σ-fst= (! Lift≡id) _
    Σᵉ-adq-exploreAny (leaf x₁) F     = Σᵉ-adq-explore-P x₁ F
    Σᵉ-adq-exploreAny (fork xs xs₁) F = ⊎= (Σᵉ-adq-exploreAny xs _) (Σᵉ-adq-exploreAny xs₁ _) ∙ ! dist-⊎-Σ

  exploreΣᵉ : ∀ {m} xs → Explore m (Σᵉ (fromBinTree xs) P)
  exploreΣᵉ {m} xs = fromBinTree-ind xs (λ e → Explore m (Σᵉ e P)) Lift𝟘ᵉ _⊎ᵉ_ explore-P

  module _ (Σᵉ-adq-explore-P : ∀ {m} x → Adequate-Σᵉ {m} (explore-P x)) where
    Σᵉ-adq-exploreΣᵉ : ∀ {m} xs → Adequate-Σᵉ {m} (exploreΣᵉ xs)
    Σᵉ-adq-exploreΣᵉ empty F         = ! Σ𝟘-lift∘fst ∙ Σ-fst= (! Lift≡id) _
    Σᵉ-adq-exploreΣᵉ (leaf x₁) F     = Σᵉ-adq-explore-P x₁ F
    Σᵉ-adq-exploreΣᵉ (fork xs xs₁) F = ⊎= (Σᵉ-adq-exploreΣᵉ xs _) (Σᵉ-adq-exploreΣᵉ xs₁ _) ∙ ! dist-⊎-Σ

-- -}
-- -}
-- -}
-- -}
