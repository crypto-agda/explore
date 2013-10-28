{-# OPTIONS --without-K #-}
open import Type hiding (★)
open import Function
open import Relation.Binary.PropositionalEquality

open import Explore.Core
open import Explore.Properties

-- Explore ℓ is not an endo functor because of universe levels
module Explore.Monad ℓ where

M = Explore ℓ

module _ {A : Set} where
    return : A → M A
    return = point-explore

    mzero : M A
    mzero = empty-explore

    mplus : M A → M A → M A
    mplus = merge-explore

    module _ {p} where
        return-ind : ∀ x → ExploreInd p (return x)
        return-ind = point-explore-ind

        mzero-ind : ExploreInd p mzero
        mzero-ind = empty-explore-ind

        mplus-ind : ∀ {e₀ e₁ : M A}
                    → ExploreInd p e₀ → ExploreInd p e₁
                    → ExploreInd p (merge-explore e₀ e₁)
        mplus-ind Pe₀ Pe₁ P Pε _P∙_ Pf = (Pe₀ P Pε _P∙_ Pf) P∙ (Pe₁ P Pε _P∙_ Pf)

module _ {A B : Set} where

    infixl 1 _>>=_ _>>=-ind_
    _>>=_ : M A → (A → M B) → M B
    (expᴬ >>= expᴮ) ε _∙_ f = expᴬ ε _∙_ λ x → expᴮ x ε _∙_ f

    _>>=-ind_ : ∀ {p}
                  {expᴬ : M A} → ExploreInd p expᴬ →
                  {expᴮ : A → M B} → (∀ x → ExploreInd p (expᴮ x))
               → ExploreInd p (expᴬ >>= expᴮ)
    _>>=-ind_ {expᴬ} Pᴬ {expᴮ} Pᴮ P Pz _P∙_ Pf
      = Pᴬ (λ e → P (e >>= expᴮ)) Pz _P∙_ λ x → Pᴮ x P Pz _P∙_ Pf

    map : (A → B) → M A → M B
    map f e = e >>= return ∘ f

    map-ind : ∀ {p} (f : A → B) {expᴬ : M A} → ExploreInd p expᴬ → ExploreInd p (map f expᴬ)
    map-ind f Pᴬ = Pᴬ >>=-ind return-ind ∘ f

    private
        {- This law is for free: map f e = e >>= return ∘ f -}
        map' : (A → B) → M A → M B
        map' f exp ε _∙_ g = exp ε _∙_ (g ∘ f)

        map'≡map : map' ≡ map
        map'≡map = refl

-- universe issues...
-- join : M (M A) → M A

module _ {A B C : Set} (m : M A) (f : A → M B) (g : B → M C) where
    infix 0 _≡e_
    _≡e_ = λ {A} → _≡_ {A = M A}

    left-identity : f ≡ (λ x → return x >>= f)
    left-identity = refl

    right-identity : m ≡e m >>= return
    right-identity = refl

    associativity : m >>= (λ x → f x >>= g) ≡e (m >>= f) >>= g
    associativity = refl
