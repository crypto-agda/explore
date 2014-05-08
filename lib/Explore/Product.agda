{-# OPTIONS --without-K #-}
{- The main definitions are the following:

  * exploreΣ
  * exploreΣ-ind
  * adequate-sumΣ
-}

open import Level.NP
open import Type hiding (★)
open import Type.Identities
open import Function.NP
open import Function.Extensionality
open import Data.Two
open import Data.Product.NP
open import Data.Fin
open import Relation.Binary.Logical
open import Relation.Binary.PropositionalEquality.NP using (_≡_ ; module ≡-Reasoning; !_; _∙_; coe; tr)
open import HoTT
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

module _
    {ℓ₀ ℓ₁ ℓᵣ}
    {A₀ A₁} {Aᵣ : ⟦★₀⟧ A₀ A₁}
    {B₀ : A₀ → _} {B₁ : A₁ → _} {Bᵣ : (Aᵣ ⟦→⟧ ⟦★₀⟧) B₀ B₁}
    {eᴬ₀ : Explore ℓ₀ A₀} {eᴬ₁ : Explore ℓ₁ A₁}(eᴬᵣ : ⟦Explore⟧ᵤ ℓ₀ ℓ₁ ℓᵣ Aᵣ eᴬ₀ eᴬ₁)
    {eᴮ₀ : ∀ {x} → Explore ℓ₀ (B₀ x)} {eᴮ₁ : ∀ {x} → Explore ℓ₁ (B₁ x)}(eᴮᵣ : ∀ {x₀ x₁}(x : Aᵣ x₀ x₁) → ⟦Explore⟧ᵤ ℓ₀ ℓ₁ ℓᵣ (Bᵣ x) (eᴮ₀ {x₀}) (eᴮ₁ {x₁}))
    where
   ⟦exploreΣ⟧ : ⟦Explore⟧ᵤ _ _ ℓᵣ (⟦Σ⟧ Aᵣ Bᵣ) (exploreΣ eᴬ₀ (λ {x} → eᴮ₀ {x})) (exploreΣ eᴬ₁ (λ {x} → eᴮ₁ {x}))
   ⟦exploreΣ⟧ P Pε P∙ Pf = eᴬᵣ P Pε P∙ (λ {x₀} {x₁} x → eᴮᵣ x P Pε P∙ (λ xᵣ → Pf (x ⟦,⟧ xᵣ)))

module _ {A} {B : A → ★₀} {sumᴬ : Sum A} {sumᴮ : ∀ {x} → Sum (B x)}{{_ : FunExt}}{{_ : UA}} where

    private
        sumᴬᴮ = sumᴬ ⟨,⟩ (λ {x} → sumᴮ {x})

    adequate-sumΣ : Adequate-sum sumᴬ → (∀ {x} → Adequate-sum (sumᴮ {x})) → Adequate-sum sumᴬᴮ
    adequate-sumΣ asumᴬ asumᴮ f
      = Fin (sumᴬᴮ f)
      ≡⟨by-definition⟩
        Fin (sumᴬ (λ a → sumᴮ (λ b → f (a , b))))
      ≡⟨ asumᴬ _ ⟩
        Σ A (λ a → Fin (sumᴮ (λ b → f (a , b))))
      ≡⟨ Σ=′ _ (λ _ → asumᴮ _) ⟩
        Σ A (λ a → Σ (B a) (λ b → Fin (f (a , b))))
      ≡⟨ Σ-assoc ⟩
        Σ (Σ A B) (Fin ∘ f)
      ∎
      where open ≡-Reasoning

-- From now on, these are derived definitions for convenience and pedagogical reasons

explore× : ∀ {m A B} → Explore m A → Explore m B → Explore m (A × B)
explore× exploreᴬ exploreᴮ = exploreΣ exploreᴬ exploreᴮ

module _ {ℓ₀ ℓ₁ ℓᵣ A₀ A₁ B₀ B₁}
         {Aᵣ  : ⟦★₀⟧ A₀ A₁}
         {Bᵣ  : ⟦★₀⟧ B₀ B₁}
         {eᴬ₀ : Explore ℓ₀ A₀} {eᴬ₁ : Explore ℓ₁ A₁}(eᴬᵣ : ⟦Explore⟧ᵤ ℓ₀ ℓ₁ ℓᵣ Aᵣ eᴬ₀ eᴬ₁)
         {eᴮ₀ : Explore ℓ₀ B₀} {eᴮ₁ : Explore ℓ₁ B₁}(eᴮᵣ : ⟦Explore⟧ᵤ ℓ₀ ℓ₁ ℓᵣ Bᵣ eᴮ₀ eᴮ₁)
    where
    ⟦explore×⟧ : ⟦Explore⟧ᵤ _ _ ℓᵣ (Aᵣ ⟦×⟧ Bᵣ) (explore× eᴬ₀ eᴮ₀) (explore× eᴬ₁ eᴮ₁)
    ⟦explore×⟧ P Pε P∙ Pf = eᴬᵣ P Pε P∙ (λ x → eᴮᵣ P Pε P∙ (λ y → Pf (_⟦,⟧_ x y)))

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
    help = [0: sum-zero μB 1: uB y ]
-}

{-
module _ {A} {Aₚ : A → ★₀} {B : A → _} {eᴬ : Explore ₁ A} (eᴬₚ : [Explore] _ _ Aₚ eᴬ) (eᴬ-ind : ExploreInd (ₛ ₀) eᴬ) {eᴮ : ∀ {x} → Explore ₀ (B x)} where
  open import Explore.One
  --open import Explore.Product
  exploreΠᵉ : Explore ₀ (Πᵉ eᴬ B)
  exploreΠᵉ = eᴬ-ind (λ e → Explore ₀ (Πᵉ e B)) (λ ε _∙₁_ x → x _) explore× (λ x → eᴮ {x})

  exploreΠᵉ' : Explore ₀ (Πᵉ eᴬ B)
  exploreΠᵉ' = λ {M} ε _∙₁_ x → {!eᴬₚ (const (Lift M))!}

  exploreΠᵉ-ind : ExploreInd ₁ exploreΠᵉ
  exploreΠᵉ-ind = {!⟦Explore⟧ᵤ _ _ _ eᴬ!}
-}

module _ {ℓ} {A} {B : A → _} {eᴬ : Explore (ₛ ℓ) A} {eᴮ : ∀ {x} → Explore (ₛ ℓ) (B x)} where
  private
    eᴬᴮ = exploreΣ eᴬ λ {x} → eᴮ {x}

  focusΣ : Focus eᴬ → (∀ {x} → Focus (eᴮ {x})) → Focus eᴬᴮ
  focusΣ fᴬ fᴮ ((x , y) , z) = fᴬ (x , fᴮ (y , z))

  lookupΣ : Lookup eᴬ → (∀ {x} → Lookup (eᴮ {x})) → Lookup eᴬᴮ
  lookupΣ lookupᴬ lookupᴮ d = uncurry (lookupᴮ ∘ lookupᴬ d)

  -- can also be derived from explore-ind
  reifyΣ : Reify eᴬ → (∀ {x} → Reify (eᴮ {x})) → Reify eᴬᴮ
  reifyΣ reifyᴬ reifyᴮ f = reifyᴬ (reifyᴮ ∘ curry f)

  ΣᵉΣ-ok : {{_ : UA}}{{_ : FunExt}} → Adequate-Σᵉ eᴬ → (∀ {x} → Adequate-Σᵉ (eᴮ {x})) → Adequate-Σᵉ eᴬᴮ
  ΣᵉΣ-ok eᴬ eᴮ f = eᴬ _ ∙ Σ=′ _ (λ _ → eᴮ _) ∙ Σ-assoc

  ΠᵉΣ-ok : {{_ : UA}}{{_ : FunExt}} → Adequate-Πᵉ eᴬ → (∀ {x} → Adequate-Πᵉ (eᴮ {x})) → Adequate-Πᵉ eᴬᴮ
  ΠᵉΣ-ok eᴬ eᴮ f = eᴬ _ ∙ Π=′ _ (λ _ → eᴮ _) ∙ ! ΠΣ-curry

module _ {ℓ} {A B} {eᴬ : Explore (ₛ ℓ) A} {eᴮ : Explore (ₛ ℓ) B} where
  private
    eᴬᴮ = explore× eᴬ eᴮ

  focus× : Focus eᴬ → Focus eᴮ → Focus eᴬᴮ
  focus× fᴬ fᴮ = focusΣ {eᴬ = eᴬ} {eᴮ = eᴮ} fᴬ fᴮ

  lookup× : Lookup eᴬ → Lookup eᴮ → Lookup eᴬᴮ
  lookup× fᴬ fᴮ = lookupΣ {eᴬ = eᴬ} {eᴮ = eᴮ} fᴬ fᴮ

  Σᵉ×-ok : {{_ : UA}}{{_ : FunExt}} → Adequate-Σᵉ eᴬ → Adequate-Σᵉ eᴮ → Adequate-Σᵉ eᴬᴮ
  Σᵉ×-ok eᴬ eᴮ f = eᴬ _ ∙ Σ=′ _ (λ _ → eᴮ _) ∙ Σ-assoc

  Πᵉ×-ok : {{_ : UA}}{{_ : FunExt}} → Adequate-Πᵉ eᴬ → Adequate-Πᵉ eᴮ → Adequate-Πᵉ eᴬᴮ
  Πᵉ×-ok eᴬ eᴮ f = eᴬ _ ∙ Π=′ _ (λ _ → eᴮ _) ∙ ! ΠΣ-curry

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
