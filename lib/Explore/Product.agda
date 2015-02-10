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
open import Relation.Binary.PropositionalEquality.NP using (_≡_ ; module ≡-Reasoning; !_; _∙_; coe; tr; ap; ap₂; J-orig)
open import HoTT
open import Category.Monad.Continuation.Alias

open import Explore.Core
open import Explore.Properties
import Explore.Monad as EM
open import Explore.Explorable

module Explore.Product where

module _ {m a b} {A : ★ a} {B : A → ★ b} where
    exploreΣ : Explore m A → (∀ {x} → Explore m (B x)) → Explore m (Σ A B)
    exploreΣ exploreᴬ exploreᴮ ε _⊕_ = exploreᴬ ε _⊕_ ⟨,⟩ exploreᴮ ε _⊕_

    module _ {eᴬ : Explore m A} {eᴮ : ∀ {x} → Explore m (B x)} where

        exploreΣ-ind : ∀ {p} → ExploreInd p eᴬ → (∀ {x} → ExploreInd p (eᴮ {x})) → ExploreInd p (exploreΣ eᴬ eᴮ)
        exploreΣ-ind Peᴬ Peᴮ P Pε P⊕ Pf =
          Peᴬ (λ e → P (λ _ _ _ → e _ _ _)) Pε P⊕ (λ x → Peᴮ {x} (λ e → P (λ _ _ _ → e _ _ _)) Pε P⊕ (curry Pf x))

module _
    {ℓ₀ ℓ₁ ℓᵣ}
    {a₀ a₁ aᵣ} {A₀ : ★ a₀} {A₁ : ★ a₁} {Aᵣ : ⟦★⟧ aᵣ A₀ A₁}
    {b₀ b₁ bᵣ} {B₀ : A₀ → ★ b₀} {B₁ : A₁ → ★ b₁} {Bᵣ : (Aᵣ ⟦→⟧ ⟦★⟧ bᵣ) B₀ B₁}
    {eᴬ₀ : Explore ℓ₀ A₀} {eᴬ₁ : Explore ℓ₁ A₁}(eᴬᵣ : ⟦Explore⟧ ℓᵣ Aᵣ eᴬ₀ eᴬ₁)
    {eᴮ₀ : ∀ {x} → Explore ℓ₀ (B₀ x)} {eᴮ₁ : ∀ {x} → Explore ℓ₁ (B₁ x)}(eᴮᵣ : ∀ {x₀ x₁}(x : Aᵣ x₀ x₁) → ⟦Explore⟧ ℓᵣ (Bᵣ x) (eᴮ₀ {x₀}) (eᴮ₁ {x₁}))
    where
   ⟦exploreΣ⟧ : ⟦Explore⟧ ℓᵣ (⟦Σ⟧ Aᵣ Bᵣ) (exploreΣ eᴬ₀ (λ {x} → eᴮ₀ {x})) (exploreΣ eᴬ₁ (λ {x} → eᴮ₁ {x}))
   ⟦exploreΣ⟧ P Pε P⊕ Pf = eᴬᵣ P Pε P⊕ (λ {x₀} {x₁} x → eᴮᵣ x P Pε P⊕ (λ xᵣ → Pf (x ⟦,⟧ xᵣ)))

module _
    {ℓ₀ ℓ₁ ℓᵣ}
    {a} {A : ★ a}
    {b} {B : A → ★ b}
    {eᴬ₀ : Explore ℓ₀ A} {eᴬ₁ : Explore ℓ₁ A}(eᴬᵣ : ⟦Explore⟧ ℓᵣ _≡_ eᴬ₀ eᴬ₁)
    {eᴮ₀ : ∀ {x} → Explore ℓ₀ (B x)} {eᴮ₁ : ∀ {x} → Explore ℓ₁ (B x)}
    (eᴮᵣ : ∀ x → ⟦Explore⟧ ℓᵣ _≡_ (eᴮ₀ {x}) (eᴮ₁ {x}))
    where
   ⟦exploreΣ⟧≡ : ⟦Explore⟧ ℓᵣ _≡_ (exploreΣ eᴬ₀ (λ {x} → eᴮ₀ {x})) (exploreΣ eᴬ₁ (λ {x} → eᴮ₁ {x}))
   ⟦exploreΣ⟧≡ {P₀} {P₁} P {ε₀} {ε₁} Pε {⊕₀} {⊕₁} P⊕ {f₀} {f₁} Pf
     = eᴬᵣ P Pε P⊕ λ {x₀} {x₁} x → J-orig (λ x₀ x₁ x → P (eᴮ₀ ε₀ ⊕₀ (f₀ ∘ _,_ x₀)) (eᴮ₁ ε₁ ⊕₁ (f₁ ∘ _,_ x₁)))
                                          (λ y → eᴮᵣ y P Pε P⊕ (λ xᵣ → Pf (ap (_,_ y) xᵣ))) x

module _
    {ℓ₀ ℓ₁ ℓᵣ}
    {a} {A : ★ a}
    {b} {B : A → ★ b}
    {eᴬ₀ : Explore ℓ₀ A} {eᴬ₁ : Explore ℓ₁ A}(eᴬᵣ : ⟦Explore⟧ ℓᵣ _≡_ eᴬ₀ eᴬ₁)
    {eᴮ₀ : ∀ {x} → Explore ℓ₀ (B x)} {eᴮ₁ : ∀ {x} → Explore ℓ₁ (B x)}
    (eᴮᵣ : ∀ {x₀ x₁} (x : x₀ ≡ x₁) → ⟦Explore⟧ ℓᵣ (λ b₀ b₁ → tr B x b₀ ≡ b₁) (eᴮ₀ {x₀}) (eᴮ₁ {x₁}))
    where
   ⟦exploreΣ⟧≡' : ⟦Explore⟧ ℓᵣ _≡_ (exploreΣ eᴬ₀ (λ {x} → eᴮ₀ {x})) (exploreΣ eᴬ₁ (λ {x} → eᴮ₁ {x}))
   ⟦exploreΣ⟧≡' P Pε P⊕ Pf = eᴬᵣ P Pε P⊕ (λ {x₀} {x₁} x → eᴮᵣ {x₀} {x₁} x P Pε P⊕ (λ xᵣ → Pf (pair= x xᵣ)))

module _ {A : ★₀} {B : A → ★₀} {sumᴬ : Sum A} {sumᴮ : ∀ {x} → Sum (B x)}{{_ : FunExt}}{{_ : UA}} where
    private
        sumᴬᴮ : Sum (Σ A B)
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

explore× : ∀ {m a b} {A : ★ a} {B : ★ b} → Explore m A → Explore m B → Explore m (A × B)
explore× exploreᴬ exploreᴮ = exploreΣ exploreᴬ exploreᴮ

explore×-ind : ∀ {m p a b} {A : ★ a} {B : ★ b} {eᴬ : Explore m A} {eᴮ : Explore m B}
               → ExploreInd p eᴬ → ExploreInd p eᴮ
               → ExploreInd p (explore× eᴬ eᴮ)
explore×-ind Peᴬ Peᴮ = exploreΣ-ind Peᴬ Peᴮ

sumΣ : ∀ {a b} {A : ★ a} {B : A → ★ b} → Sum A → (∀ {x} → Sum (B x)) → Sum (Σ A B)
sumΣ = _⟨,⟩_

sum× : ∀ {a b} {A : ★ a} {B : ★ b} → Sum A → Sum B → Sum (A × B)
sum× = _⟨,⟩′_

module _ {ℓ₀ ℓ₁ ℓᵣ A₀ A₁ B₀ B₁}
         {Aᵣ  : ⟦★₀⟧ A₀ A₁}
         {Bᵣ  : ⟦★₀⟧ B₀ B₁}
         {eᴬ₀ : Explore ℓ₀ A₀} {eᴬ₁ : Explore ℓ₁ A₁}(eᴬᵣ : ⟦Explore⟧ ℓᵣ Aᵣ eᴬ₀ eᴬ₁)
         {eᴮ₀ : Explore ℓ₀ B₀} {eᴮ₁ : Explore ℓ₁ B₁}(eᴮᵣ : ⟦Explore⟧ ℓᵣ Bᵣ eᴮ₀ eᴮ₁)
    where
    ⟦explore×⟧ : ⟦Explore⟧ ℓᵣ (Aᵣ ⟦×⟧ Bᵣ) (explore× eᴬ₀ eᴮ₀) (explore× eᴬ₁ eᴮ₁)
    ⟦explore×⟧ P Pε P⊕ Pf = eᴬᵣ P Pε P⊕ (λ x → eᴮᵣ P Pε P⊕ (λ y → Pf (_⟦,⟧_ x y)))

module _ {ℓ₀ ℓ₁ ℓᵣ} {A B : ★₀}
         {eᴬ₀ : Explore ℓ₀ A} {eᴬ₁ : Explore ℓ₁ A}(eᴬᵣ : ⟦Explore⟧ ℓᵣ _≡_ eᴬ₀ eᴬ₁)
         {eᴮ₀ : Explore ℓ₀ B} {eᴮ₁ : Explore ℓ₁ B}(eᴮᵣ : ⟦Explore⟧ ℓᵣ _≡_ eᴮ₀ eᴮ₁)
    where
    ⟦explore×⟧≡ : ⟦Explore⟧ ℓᵣ _≡_ (explore× eᴬ₀ eᴮ₀) (explore× eᴬ₁ eᴮ₁)
    ⟦explore×⟧≡ P Pε P⊕ Pf = eᴬᵣ P Pε P⊕ (λ x → eᴮᵣ P Pε P⊕ (λ y → Pf (ap₂ _,_ x y)))

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

module _ {ℓ a b} {A : ★ a} {B : A → ★ b} {eᴬ : Explore (ₛ ℓ) A} {eᴮ : ∀ {x} → Explore (ₛ ℓ) (B x)} where
  private
    eᴬᴮ = exploreΣ eᴬ λ {x} → eᴮ {x}

  focusΣ : Focus eᴬ → (∀ {x} → Focus (eᴮ {x})) → Focus eᴬᴮ
  focusΣ fᴬ fᴮ ((x , y) , z) = fᴬ (x , fᴮ (y , z))

  lookupΣ : Lookup eᴬ → (∀ {x} → Lookup (eᴮ {x})) → Lookup eᴬᴮ
  lookupΣ lookupᴬ lookupᴮ d = uncurry (lookupᴮ ∘ lookupᴬ d)

  -- can also be derived from explore-ind
  reifyΣ : Reify eᴬ → (∀ {x} → Reify (eᴮ {x})) → Reify eᴬᴮ
  reifyΣ reifyᴬ reifyᴮ f = reifyᴬ (reifyᴮ ∘ curry f)

module _ {ℓ} {A : ★₀} {B : A → ★₀}
         {eᴬ : Explore (ₛ ℓ) A} {eᴮ : ∀ {x} → Explore (ₛ ℓ) (B x)}
         {{_ : UA}}{{_ : FunExt}} where
  private
    eᴬᴮ = exploreΣ eᴬ λ {x} → eᴮ {x}

  ΣᵉΣ-ok : Adequate-Σ (Σᵉ eᴬ) → (∀ {x} → Adequate-Σ (Σᵉ (eᴮ {x}))) → Adequate-Σ (Σᵉ eᴬᴮ)
  ΣᵉΣ-ok eᴬ eᴮ f = eᴬ _ ∙ Σ=′ _ (λ _ → eᴮ _) ∙ Σ-assoc

  ΠᵉΣ-ok : Adequate-Π (Πᵉ eᴬ) → (∀ {x} → Adequate-Π (Πᵉ (eᴮ {x}))) → Adequate-Π (Πᵉ eᴬᴮ)
  ΠᵉΣ-ok eᴬ eᴮ f = eᴬ _ ∙ Π=′ _ (λ _ → eᴮ _) ∙ ! ΠΣ-curry

module _ {ℓ a b} {A : ★ a} {B : ★ b} {eᴬ : Explore (ₛ ℓ) A} {eᴮ : Explore (ₛ ℓ) B} where
  private
    eᴬᴮ = explore× eᴬ eᴮ

  focus× : Focus eᴬ → Focus eᴮ → Focus eᴬᴮ
  focus× fᴬ fᴮ = focusΣ {eᴬ = eᴬ} {eᴮ = eᴮ} fᴬ fᴮ

  lookup× : Lookup eᴬ → Lookup eᴮ → Lookup eᴬᴮ
  lookup× fᴬ fᴮ = lookupΣ {eᴬ = eᴬ} {eᴮ = eᴮ} fᴬ fᴮ

module _ {ℓ} {A B : ★₀} {eᴬ : Explore (ₛ ℓ) A} {eᴮ : Explore (ₛ ℓ) B} where
  private
    eᴬᴮ = explore× eᴬ eᴮ

  Σᵉ×-ok : {{_ : UA}}{{_ : FunExt}} → Adequate-Σ (Σᵉ eᴬ) → Adequate-Σ (Σᵉ eᴮ) → Adequate-Σ (Σᵉ eᴬᴮ)
  Σᵉ×-ok eᴬ eᴮ f = eᴬ _ ∙ Σ=′ _ (λ _ → eᴮ _) ∙ Σ-assoc

  Πᵉ×-ok : {{_ : UA}}{{_ : FunExt}} → Adequate-Π (Πᵉ eᴬ) → Adequate-Π (Πᵉ eᴮ) → Adequate-Π (Πᵉ eᴬᴮ)
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
    fst-explore : ∀ {m} {A : ★₀} {B : A → ★₀} → Explore m (Σ A B) → Explore m A
    fst-explore = EM.map _ fst

    snd-explore : ∀ {m} {A B : ★₀} → Explore m (A × B) → Explore m B
    snd-explore = EM.map _ snd

    sum'Σ : ∀ {A : ★₀} {B : A → ★₀} → Sum A → (∀ x → Sum (B x)) → Sum (Σ A B)
    sum'Σ sumᴬ sumᴮ f = sumᴬ (λ x₀ →
                          sumᴮ x₀ (λ x₁ →
                            f (x₀ , x₁)))

    explore×' : ∀ {A B : ★₀} → Explore₀ A → Explore _ B → Explore _ (A × B)
    explore×' exploreᴬ exploreᴮ ε _⊕_ f = exploreᴬ ε _⊕_ (λ x → exploreᴮ ε _⊕_ (curry f x))

    explore×-ind' : ∀ {A B} {eᴬ : Explore _ A} {eᴮ : Explore _ B}
                    → ExploreInd₀ eᴬ → ExploreInd₀ eᴮ → ExploreInd₀ (explore×' eᴬ eᴮ)
    explore×-ind' Peᴬ Peᴮ P Pε P⊕ Pf =
      Peᴬ (λ e → P (λ _ _ _ → e _ _ _)) Pε P⊕ (Peᴮ (λ e → P (λ _ _ _ → e _ _ _)) Pε P⊕ ∘ curry Pf)

    -- liftM2 _,_ in the continuation monad
    sum×' : ∀ {A B : ★₀} → Sum A → Sum B → Sum (A × B)
    sum×' sumᴬ sumᴮ f = sumᴬ λ x₀ →
                          sumᴮ λ x₁ →
                            f (x₀ , x₁)
-- -}
-- -}
-- -}
