{-# OPTIONS --without-K #-}
{- The main definitions are the following:

  * exploreΣ
  * exploreΣ-ind
  * adequate-sumΣ
-}

open import Level.NP
open import Type hiding (★)
open import Function.NP
import Function.Related as FR
import Function.Inverse.NP as FI
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP
open import Data.Bool using (true ; false ; _∧_ ; if_then_else_)
open import Data.Product
open import Data.Fin
open import Relation.Binary.PropositionalEquality.NP using (_≡_ ; module ≡-Reasoning)
open import Category.Monad.Continuation.Alias

open import Explore.Core
open import Explore.Properties
import Explore.Monad as EM
open import Explore.Explorable

module Explore.Product where

module _ {m A} {B : A → ★₀} where

    exploreΣ : Explore m A → (∀ {x} → Explore m (B x)) → Explore m (Σ A B)
    exploreΣ exploreᴬ exploreᴮ z op = exploreᴬ z op ⟨,⟩ exploreᴮ z op

    module _ {eᴬ : Explore m A} {eᴮ : ∀ {x} → Explore m (B x)} where

        exploreΣ-ind : ∀ {p} → ExploreInd p eᴬ → (∀ {x} → ExploreInd p (eᴮ {x})) → ExploreInd p (exploreΣ eᴬ eᴮ)
        exploreΣ-ind Peᴬ Peᴮ P Pz P∙ Pf =
          Peᴬ (λ e → P (λ _ _ _ → e _ _ _)) Pz P∙ (λ x → Peᴮ {x} (λ e → P (λ _ _ _ → e _ _ _)) Pz P∙ (curry Pf x))

module _ {A}{B : A → ★₀}{eᴬ : Explore ₀ A}{eᴮ : ∀ {x} → Explore ₀ (B x)} where
   explore⊎-adq : AdequateExplore eᴬ → (∀ {x} → AdequateExplore (eᴮ {x})) → AdequateExplore (exploreΣ eᴬ eᴮ)
   explore⊎-adq aᴬ aᴮ F ε _⊕_ f F-proof
     = F (big⊕ᴬ (λ a → big⊕ᴮ (λ b → f (a , b))))
     ↔⟨ aᴬ F _ _ _ F-proof ⟩
         Σ A (F ∘ (λ a → big⊕ᴮ (λ b → f (a , b))))
     ↔⟨ second-iso (λ _ → aᴮ F _ _ _ F-proof) ⟩
       Σ A (λ a → Σ (B a) (λ b → F (f (a , b))))
     ↔⟨ FI.sym Σ-assoc ⟩
       Σ (Σ A B) (F ∘ f)
     ∎
     where open FR.EquationalReasoning
           big⊕ᴬ = eᴬ ε _⊕_
           big⊕ᴮ = λ {x} → eᴮ {x} ε _⊕_

module _ {A} {B : A → ★₀} {sumᴬ : Sum A} {sumᴮ : ∀ {x} → Sum (B x)} where

    private
        sumᴬᴮ = sumᴬ ⟨,⟩ (λ {x} → sumᴮ {x})

    adequate-sumΣ : AdequateSum sumᴬ → (∀ {x} → AdequateSum (sumᴮ {x})) → AdequateSum sumᴬᴮ
    adequate-sumΣ asumᴬ asumᴮ f = Fin (sumᴬᴮ f)
                                ↔⟨ FI.id ⟩
                                  Fin (sumᴬ (λ a → sumᴮ (λ b → f (a , b))))
                                ↔⟨ asumᴬ _ ⟩
                                  Σ A (λ a → Fin (sumᴮ (λ b → f (a , b))))
                                ↔⟨ second-iso (λ _ → asumᴮ _) ⟩
                                  Σ A (λ a → Σ (B a) (λ b → Fin (f (a , b))))
                                ↔⟨ FI.sym Σ-assoc ⟩
                                  Σ (Σ A B) (Fin ∘ f)
                                ∎
      where open FR.EquationalReasoning

-- From now on, these are derived definitions for convenience and pedagogical reasons

explore× : ∀ {m A B} → Explore m A → Explore m B → Explore m (A × B)
explore× exploreᴬ exploreᴮ = exploreΣ exploreᴬ exploreᴮ

explore×-ind : ∀ {m p A B} {eᴬ : Explore m A} {eᴮ : Explore m B}
               → ExploreInd p eᴬ → ExploreInd p eᴮ
               → ExploreInd p (explore× eᴬ eᴮ)
explore×-ind Peᴬ Peᴮ = exploreΣ-ind Peᴬ Peᴮ

sumΣ : ∀ {A} {B : A → ★₀} → Sum A → (∀ {x} → Sum (B x)) → Sum (Σ A B)
sumΣ = _⟨,⟩_

sum× : ∀ {A B} → Sum A → Sum B → Sum (A × B)
sum× = _⟨,⟩′_

{-
μΣ : ∀ {A} {B : A → ★ _} → Explorable A → (∀ {x} → Explorable (B x)) → Explorable (Σ A B)
μΣ μA μB = mk _ (exploreΣ-ind (explore-ind μA) (explore-ind μB))
                (adequate-sumΣ (adequate-sum μA) (adequate-sum μB))

infixr 4 _×-μ_
_×-μ_ : ∀ {A B} → Explorable A → Explorable B → Explorable (A × B)
μA ×-μ μB = μΣ μA μB

_×-cmp_ : ∀ {A B : ★₀ } → Cmp A → Cmp B → Cmp (A × B)
(ca ×-cmp cb) (a , b) (a' , b') = ca a a' ∧ cb b b'

×-unique : ∀ {A B}(μA : Explorable A)(μB : Explorable B)(cA : Cmp A)(cB : Cmp B)
           → Unique cA (count μA) → Unique cB (count μB) → Unique (cA ×-cmp cB) (count (μA ×-μ μB))
×-unique μA μB cA cB uA uB (x , y) = count (μA ×-μ μB) ((cA ×-cmp cB) (x , y)) ≡⟨ explore-ext μA _ (λ x' → help (cA x x')) ⟩
                                     count μA (cA x) ≡⟨ uA x ⟩
                                     1 ∎
  where
    open ≡-Reasoning
    help : ∀ b → count μB (λ y' → b ∧ cB y y') ≡ (if b then 1 else 0)
    help true = uB y
    help false = sum-zero μB
-}

module _ {ℓ} {A} {B : A → _} {eᴬ : Explore (ₛ ℓ) A} {eᴮ : ∀ {x} → Explore (ₛ ℓ) (B x)} where
  focusΣ : Focus eᴬ → (∀ {x} → Focus (eᴮ {x})) → Focus (exploreΣ eᴬ (λ {x} → eᴮ {x}))
  focusΣ fᴬ fᴮ ((x , y) , z) = fᴬ (x , fᴮ (y , z))

  lookupΣ : Lookup eᴬ → (∀ {x} → Lookup (eᴮ {x})) → Lookup (exploreΣ eᴬ (λ {x} → eᴮ {x}))
  lookupΣ lookupᴬ lookupᴮ d = uncurry (lookupᴮ ∘ lookupᴬ d)

  -- can also be derived from explore-ind
  reifyΣ : Reify eᴬ → (∀ {x} → Reify (eᴮ {x})) → Reify (exploreΣ eᴬ (λ {x} → eᴮ {x}))
  reifyΣ reifyᴬ reifyᴮ f = reifyᴬ (reifyᴮ ∘ curry f)

module _ {ℓ} {A B} {eᴬ : Explore (ₛ ℓ) A} {eᴮ : Explore (ₛ ℓ) B} where
  focus× : Focus eᴬ → Focus eᴮ → Focus (explore× eᴬ eᴮ)
  focus× fᴬ fᴮ = focusΣ {eᴬ = eᴬ} {eᴮ = eᴮ} fᴬ fᴮ
  lookup× : Lookup eᴬ → Lookup eᴮ → Lookup (explore× eᴬ eᴮ)
  lookup× fᴬ fᴮ = lookupΣ {eᴬ = eᴬ} {eᴮ = eᴮ} fᴬ fᴮ

module Operators where
    infixr 4 _×ᵉ_ _×ⁱ_ _×ˢ_
    _×ᵉ_ = explore×
    _×ⁱ_ = explore×-ind
    _×ᵃ_ = adequate-sumΣ
    _×ˢ_ = sum×
    _×ᶠ_ = focus×
    _×ˡ_ = lookup×

-- Those are here only for pedagogical use
private
    proj₁-explore : ∀ {m A} {B : A → ★ _} → Explore m (Σ A B) → Explore m A
    proj₁-explore = EM.map _ proj₁

    proj₂-explore : ∀ {m A B} → Explore m (A × B) → Explore m B
    proj₂-explore = EM.map _ proj₂

    sum'Σ : ∀ {A} {B : A → ★₀} → Sum A → (∀ x → Sum (B x)) → Sum (Σ A B)
    sum'Σ sumᴬ sumᴮ f = sumᴬ (λ x₀ →
                          sumᴮ x₀ (λ x₁ →
                            f (x₀ , x₁)))

    explore×' : ∀ {A B} → Explore₀ A → Explore _ B → Explore _ (A × B)
    explore×' exploreᴬ exploreᴮ z op f = exploreᴬ z op (λ x → exploreᴮ z op (curry f x))

    explore×-ind' : ∀ {A B} {eᴬ : Explore _ A} {eᴮ : Explore _ B}
                    → ExploreInd₀ eᴬ → ExploreInd₀ eᴮ → ExploreInd₀ (explore×' eᴬ eᴮ)
    explore×-ind' Peᴬ Peᴮ P Pz P∙ Pf =
      Peᴬ (λ e → P (λ _ _ _ → e _ _ _)) Pz P∙ (Peᴮ (λ e → P (λ _ _ _ → e _ _ _)) Pz P∙ ∘ curry Pf)

    -- liftM2 _,_ in the continuation monad
    sum×' : ∀ {A B} → Sum A → Sum B → Sum (A × B)
    sum×' sumᴬ sumᴮ f = sumᴬ λ x₀ →
                          sumᴮ λ x₁ →
                            f (x₀ , x₁)
-- -}
-- -}
-- -}
