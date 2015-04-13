{-# OPTIONS --without-K #-}
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Function using (id; _∘_ ; flip)
open import Relation.Binary.PropositionalEquality.NP

open import Explore.Core
open import Explore.Properties
import Explore.Explorable as E

module Explore.GroupHomomorphism
         {ℓ}{A B : Set ℓ}(grpA0+ : Group A)(grpB1* : Group B)
         (f : A → B)(f-homo : GroupHomomorphism grpA0+ grpB1* f)
         where
open Additive-Group grpA0+
open Multiplicative-Group grpB1*
open GroupHomomorphism f-homo -- Prop grpA0+ grpB1* (λ {x} {y} → f-homo {x} {y})
open ≡-Reasoning

module LiftGroupHomomorphism
  {i}{I : Set i}
  {explore : ∀ {ℓ} → Explore ℓ I}
  (explore-ind : ∀ {p ℓ} → ExploreInd {ℓ} p explore)
  (g : I → A)
  where

  Σᴵ = explore 0ᵍ _+_
  Πᴵ = explore 1ᵍ _*_

  lift-hom : f (Σᴵ g) ≡ Πᴵ (f ∘ g)
  lift-hom = E.FromExploreInd.LiftHom.lift-hom explore-ind _≡_ refl trans 0ᵍ _+_ 1ᵍ _*_ *= f g 0ᵍ-hom-1ᵍ hom

-- TODO rexport form Explorable the proof is there now

module FromBigOp
  {ℓ}
  ([f] : B → A)(f-inv : ∀ {b} → f ([f] b) ≡ b)
  {X}(F : BigOp X A)
  (F= : ∀ {g₀ g₁ : A → X} → g₀ ≗ g₁ → F g₀ ≡ F g₁)
    -- BigOpStableUnder p = ∀ f → F f ≡ F (f ∘ p)
    -- TODO _+_ k has an inverse already so sui should be already true
  (sui : ∀ {k} → BigOpStableUnder F (flip _+_ k))
  (O : B → X)
  where

  _≈_ : (g₀ g₁ : B → B) → Set ℓ
  g₀ ≈ g₁ = F (O ∘ g₀ ∘ f) ≡ F (O ∘ g₁ ∘ f)

  {- How this proof can be used for crypto, in particular ElGamal to DDH

  the Group A is ℤq with modular addition as operation
  the Group B is the cyclic group with order q

  f is g^, the proof only need that it is a group homomorphism
  and that it has a right inverse

  we require that the explore (for type A) function (should work with only summation)
  is Stable under addition of A (notice that we have flip in there that is so that
  we don't need commutativity

  finally we require that the explore function respects extensionality
  -}

  {-
    This proof adds [f] m, because adding a constant is stable under the
    big op F, this addition can then be pulled homomorphically through
    f, to become a, multiplication by m.
  -}
  module _ (m : B) where
    _*m = λ x → x * m

    id≈*m : id ≈ _*m
    id≈*m =
      F (O ∘ f)           ≡⟨ sui _ ⟩
      F (O ∘ f ∘ _+[f]m)  ≡⟨ F= (λ _ → ap O lemma) ⟩
      F (O ∘ _*m ∘ f)     ∎
      where
        _+[f]m = λ x → x + [f] m

        lemma : ∀ {x} → f (x + [f] m) ≡ f x * m
        lemma {x} = f (x + [f] m)   ≡⟨ hom ⟩
                    f x * f ([f] m) ≡⟨ ap (_*_ (f x)) f-inv ⟩
                    f x * m         ∎

  module _ (m₀ m₁ : B) where
    _*m₀ = λ x → x * m₀
    _*m₁ = λ x → x * m₁

    *m₀≈*m₁ : _*m₀ ≈ _*m₁
    *m₀≈*m₁ = ! id≈*m m₀ ∙ id≈*m m₁

module FromExplore
  {ℓ}
  ([f] : B → A)(f-inv : ∀ {b} → f ([f] b) ≡ b)
  {X}(z : X)(_⊕_ : X → X → X)
  (exploreᴬ  : Explore ℓ A)
  (exploreᴬ= : ExploreExt exploreᴬ)
  (let F = exploreᴬ z _⊕_)
  (F : BigOp X A)
  (F= : ∀ {g₀ g₁ : A → X} → g₀ ≗ g₁ → F g₀ ≡ F g₁)
  (sui : ∀ {k} → BigOpStableUnder F (flip _+_ k))
  (O : B → X)
  where
  -- TODO
-- -}
-- -}
-- -}
-- -}
