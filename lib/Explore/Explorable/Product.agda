open import Type hiding (★)
open import Function.NP
import Function.Related as FR
import Function.Inverse.NP as FI
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP
open import Data.Bool using (true ; false ; _∧_ ; if_then_else_)
open import Data.Product
open import Data.Fin
open import Explore.Type
open import Explore.Explorable

open import Relation.Binary.PropositionalEquality.NP using (_≡_ ; module ≡-Reasoning)

module Explore.Explorable.Product where

private
    Cont : ∀ {a m} → ★ m → ★ a → ★ _
    Cont M A = (A → M) → M

    -- liftM2 _,_ in the continuation monad
    _,-Cont_ : ∀ {a b m} {A : ★ a} {B : A → ★ b} {M : ★ m}
               → Cont M A → (∀ {x} → Cont M (B x)) → Cont M (Σ A B)
    (fA ,-Cont fB) f = fA (fB ∘ curry f)
 -- (fA ,-Cont fB) f = fA λ x → fB λ y → f (x , y)

    _,-Cont′_ : ∀ {a b m} {A : ★ a} {B : ★ b} {M : ★ m} → Cont M A → Cont M B → Cont M (A × B)
    fA ,-Cont′ fB = fA ,-Cont fB

exploreΣ : ∀ {m A} {B : A → ★₀} → Explore m A → (∀ {x} → Explore m (B x)) → Explore m (Σ A B)
exploreΣ exploreᴬ exploreᴮ op = exploreᴬ op ,-Cont exploreᴮ op

module _ {m A} {B : A → ★₀} {sᴬ : Explore m A} {sᴮ : ∀ {x} → Explore m (B x)} where

    explore-indΣ : ∀ {p} → ExploreInd p sᴬ → (∀ {x} → ExploreInd p (sᴮ {x})) → ExploreInd p (exploreΣ sᴬ sᴮ)
    explore-indΣ Psᴬ Psᴮ P P∙ Pf =
      Psᴬ (λ s → P (λ _ _ → s _ _)) P∙ (λ x → Psᴮ {x} (λ s → P (λ _ _ → s _ _)) P∙ (curry Pf x))

module _ {A} {B : A → ★₀} {sumᴬ : Sum A} {sumᴮ : ∀ {x} → Sum (B x)} where

    private
        sumᴬᴮ = sumᴬ ,-Cont (λ {x} → sumᴮ {x})

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

μΣ : ∀ {A} {B : A → ★ _} → Explorable A → (∀ {x} → Explorable (B x)) → Explorable (Σ A B)
μΣ μA μB = mk _ (explore-indΣ (explore-ind μA) (explore-ind μB))
                (adequate-sumΣ (adequate-sum μA) (adequate-sum μB))

-- using view-explore ?
proj₁-explore : ∀ {m A} {B : A → ★ _} → Explore m (Σ A B) → Explore m A
proj₁-explore s _∙_ f = s _∙_ (f ∘ proj₁)

proj₂-explore : ∀ {m A B} → Explore m (A × B) → Explore m B
proj₂-explore s _∙_ f = s _∙_ (f ∘ proj₂)

-- From now on, these are derived definitions for convenience and pedagogical reasons

infixr 4 _×-explore_

_×-explore_ : ∀ {m A B} → Explore m A → Explore m B → Explore m (A × B)
exploreᴬ ×-explore exploreᴮ = exploreΣ exploreᴬ exploreᴮ

infixr 4 _×-μ_

_×-μ_ : ∀ {A B} → Explorable A → Explorable B → Explorable (A × B)
μA ×-μ μB = μΣ μA μB

_×-explore-ind_ : ∀ {m p A B} {sᴬ : Explore m A} {sᴮ : Explore m B}
               → ExploreInd p sᴬ → ExploreInd p sᴮ
               → ExploreInd p (sᴬ ×-explore sᴮ)
Psᴬ ×-explore-ind Psᴮ = explore-indΣ Psᴬ Psᴮ

sumΣ : ∀ {A} {B : A → ★₀} → Sum A → (∀ {x} → Sum (B x)) → Sum (Σ A B)
sumΣ = _,-Cont_

infixr 4 _×-sum_

_×-sum_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
f ×-sum g = sumΣ f g

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

module _ {A} {B : A → _} {sᴬ : Explore₁ A} {sᴮ : ∀ {x} → Explore₁ (B x)} where
  focusΣ : Focus sᴬ → (∀ {x} → Focus (sᴮ {x})) → Focus (exploreΣ sᴬ (λ {x} → sᴮ {x}))
  focusΣ fᴬ fᴮ ((x , y) , z) = fᴬ (x , fᴮ (y , z))

  lookupΣ : Lookup sᴬ → (∀ {x} → Lookup (sᴮ {x})) → Lookup (exploreΣ sᴬ (λ {x} → sᴮ {x}))
  lookupΣ lookupᴬ lookupᴮ d = uncurry (lookupᴮ ∘ lookupᴬ d)

  -- can also be derived from explore-ind
  reifyΣ : Reify sᴬ → (∀ {x} → Reify (sᴮ {x})) → Reify (exploreΣ sᴬ (λ {x} → sᴮ {x}))
  reifyΣ reifyᴬ reifyᴮ f = reifyᴬ (reifyᴮ ∘ curry f)

module _ {A B} {sᴬ : Explore₁ A} {sᴮ : Explore₁ B} where
  _×-focus_ : Focus sᴬ → Focus sᴮ → Focus (sᴬ ×-explore sᴮ)
  (fᴬ ×-focus fᴮ) = focusΣ {sᴬ = sᴬ} {sᴮ = sᴮ} fᴬ fᴮ
  _×-lookup_ : Lookup sᴬ → Lookup sᴮ → Lookup (sᴬ ×-explore sᴮ)
  (fᴬ ×-lookup fᴮ) = lookupΣ {sᴬ = sᴬ} {sᴮ = sᴮ} fᴬ fᴮ

-- Those are here only for pedagogical use
private
    sum'Σ : ∀ {A} {B : A → ★₀} → Sum A → (∀ x → Sum (B x)) → Sum (Σ A B)
    sum'Σ sumᴬ sumᴮ f = sumᴬ (λ x₀ →
                          sumᴮ x₀ (λ x₁ →
                            f (x₀ , x₁)))

    _×-explore'_ : ∀ {A B} → Explore₀ A → Explore _ B → Explore _ (A × B)
    (exploreᴬ ×-explore' exploreᴮ) op f = exploreᴬ op (λ x → exploreᴮ op (curry f x))

    _×-explore-ind'_ : ∀ {A B} {sᴬ : Explore _ A} {sᴮ : Explore _ B}
                      → ExploreInd₀ sᴬ → ExploreInd₀ sᴮ → ExploreInd₀ (sᴬ ×-explore' sᴮ)
    (Psᴬ ×-explore-ind' Psᴮ) P P∙ Pf =
      Psᴬ (λ s → P (λ _ _ → s _ _)) P∙ (Psᴮ (λ s → P (λ _ _ → s _ _)) P∙ ∘ curry Pf)

    -- liftM2 _,_ in the continuation monad
    _×-sum'_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
    (sumᴬ ×-sum' sumᴮ) f = sumᴬ (λ x₀ →
                             sumᴮ (λ x₁ →
                               f (x₀ , x₁)))
-- -}
-- -}
-- -}
