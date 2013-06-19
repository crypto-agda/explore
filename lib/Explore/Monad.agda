open import Function
open import Relation.Binary.PropositionalEquality

open import Explore.Type

module Explore.Monad ℓ where

M = Explore ℓ

module _ {A : Set} where
    return : A → M A
    return x _∙_ f = f x

    return-ind : ∀ x → ExploreInd₀ (return x)
    return-ind x P _P∙_ Pf = Pf x

module _ {A B : Set} where

    infixl 1 _>>=_ _>>=-ind_
    _>>=_ : M A → (A → M B) → M B
    (expᴬ >>= expᴮ) _∙_ f = expᴬ _∙_ λ x → expᴮ x _∙_ f

    _>>=-ind_ : ∀ {expᴬ : M A} → ExploreInd₀ expᴬ →
                 {expᴮ : A → M B} → (∀ x → ExploreInd₀ (expᴮ x))
               → ExploreInd₀ (expᴬ >>= expᴮ)
    _>>=-ind_ {expᴬ} Pᴬ {expᴮ} Pᴮ P _P∙_ Pf
      = Pᴬ (λ e → P (e >>= expᴮ)) _P∙_ λ x → Pᴮ x P _P∙_ Pf

    map : (A → B) → M A → M B
    map f e = e >>= return ∘ f

    map-ind : (f : A → B) {expᴬ : M A} → ExploreInd₀ expᴬ → ExploreInd₀ (map f expᴬ)
    map-ind f Pᴬ = Pᴬ >>=-ind return-ind ∘ f

    private
        {- This law is for free: map f e = e >>= return ∘ f -}
        map' : (A → B) → M A → M B
        map' f exp _∙_ g = exp _∙_ (g ∘ f)

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
