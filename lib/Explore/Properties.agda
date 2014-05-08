{-# OPTIONS --without-K #-}
-- The core properties behind exploration functions
module Explore.Properties where

open import Level.NP
open import Type hiding (★)
open import Function.NP using (id; _∘′_; _∘_; flip; const; Π; Cmp)
open import Algebra
import Algebra.FunctionProperties.NP as FP
open FP using (Op₂)
open import Data.Nat.NP using (_+_; _*_; _≤_; _+°_)
open import Data.Indexed
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum  using (_⊎_)
open import Data.Zero using (𝟘)
open import Data.One  using (𝟙)
open import Data.Two  using (𝟚; ✓)
open import Data.Fin  using (Fin)
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)

open import Explore.Core

-- TODO: move elsewhere
module _ {a b} where

    Injective : ∀ {A : ★ a}{B : ★ b}(f : A → B) → ★ _
    Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

    _↔_ : (A : ★ a) (B : ★ b) → ★ _
    A ↔ B = (A → B) × (B → A)

module SgrpExtra {c ℓ} (sg : Semigroup c ℓ) where
  open Semigroup sg
  open Setoid-Reasoning (Semigroup.setoid sg) public
  C : ★ _
  C = Carrier
  _≈°_ : ∀ {a} {A : ★ a} (f g : A → C) → ★ _
  f ≈° g = ∀ x → f x ≈ g x
  _∙°_   : ∀ {a} {A : ★ a} (f g : A → C) → A → C
  (f ∙° g) x = f x ∙ g x
  infixl 7 _-∙-_
  _-∙-_ : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  _-∙-_ = ∙-cong

module Sgrp {c ℓ} (sg : Semigroup c ℓ) where
  open Semigroup sg public
  open SgrpExtra sg public

module RawMon {c} {C : ★ c} (rawMon : C × Op₂ C) where
  ε    = proj₁ rawMon
  _∙_  = proj₂ rawMon

module Mon {c ℓ} (m : Monoid c ℓ) where
  open Monoid m public
  sg = semigroup
  open SgrpExtra semigroup public
  RawMon = C × Op₂ C
  rawMon : RawMon
  rawMon = ε , _∙_

module CMon {c ℓ} (cm : CommutativeMonoid c ℓ) where
  open CommutativeMonoid cm public
  sg = semigroup
  m = monoid
  open SgrpExtra sg public
  open FP _≈_

  ∙-interchange : Interchange _∙_ _∙_
  ∙-interchange = InterchangeFromAssocCommCong.∙-interchange
                    isEquivalence
                    _∙_ assoc comm (λ _ → flip ∙-cong refl)

ExploreInd : ∀ p {ℓ A} → Explore ℓ A → ★ (ₛ (ℓ ⊔ p))
ExploreInd p {ℓ} {A} exp =
  ∀ (P  : Explore ℓ A → ★ p)
    (Pε : P empty-explore)
    (P∙ : ∀ {e₀ e₁ : Explore ℓ A} → P e₀ → P e₁ → P (merge-explore e₀ e₁))
    (Pf : ∀ x → P (point-explore x))
  → P exp

module _ {ℓ p A} where
    point-explore-ind : (x : A) → ExploreInd p (point-explore {ℓ} x)
    point-explore-ind x _ _ _ Pf = Pf x

    empty-explore-ind : ExploreInd p {ℓ} {A} empty-explore
    empty-explore-ind _ Pε _ _ = Pε

    merge-explore-ind : ∀ {e₀ e₁ : Explore ℓ A}
                        → ExploreInd p e₀ → ExploreInd p e₁
                        → ExploreInd p (merge-explore e₀ e₁)
    merge-explore-ind Pe₀ Pe₁ P Pε _P∙_ Pf = (Pe₀ P Pε _P∙_ Pf) P∙ (Pe₁ P Pε _P∙_ Pf)

ExploreInd₀ : ∀ {ℓ A} → Explore ℓ A → ★ _
ExploreInd₀ = ExploreInd ₀

ExploreInd₁ : ∀ {ℓ A} → Explore ℓ A → ★ _
ExploreInd₁ = ExploreInd ₁

BigOpMonInd : ∀ p {c ℓ} {A} (M : Monoid c ℓ) → BigOpMon M A → ★ _
BigOpMonInd p {c} {ℓ} {A} M exp =
  ∀ (P  : BigOpMon M A → ★ p)
    (Pε : P (const ε))
    (P∙ : ∀ {e₀ e₁ : BigOpMon M A} → P e₀ → P e₁ → P (λ f → e₀ f ∙ e₁ f))
    (Pf : ∀ x → P (λ f → f x))
    (P≈ : ∀ {e e'} → e ≈° e' → P e → P e')
  → P exp
  where open Mon M

module _ {ℓ A} (eᴬ : Explore (ₛ ℓ) A) where
    Πᵉ : (A → ★ ℓ) → ★ ℓ
    Πᵉ = eᴬ (Lift 𝟙) _×_

    Σᵉ : (A → ★ ℓ) → ★ ℓ
    Σᵉ = eᴬ (Lift 𝟘) _⊎_

module _ {ℓ A} (eᴬ : Explore (ₛ ℓ) A) where
    Lookup : ★ (ₛ ℓ)
    Lookup = ∀ {P : A → ★ ℓ} → Πᵉ eᴬ P → Π A P

    -- alternative name suggestion: tabulate
    Reify : ★ (ₛ ℓ)
    Reify = ∀ {P : A → ★ ℓ} → Π A P → Πᵉ eᴬ P

    Unfocus : ★ (ₛ ℓ)
    Unfocus = ∀ {P : A → ★ ℓ} → Σᵉ eᴬ P → Σ A P

    -- alternative name suggestion: inject
    Focus : ★ (ₛ ℓ)
    Focus = ∀ {P : A → ★ ℓ} → Σ A P → Σᵉ eᴬ P

    Adequate-Σᵉ : ★ _
    Adequate-Σᵉ = ∀ F → Σᵉ eᴬ F ≡ Σ A F

    Adequate-Πᵉ : ★ _
    Adequate-Πᵉ = ∀ F → Πᵉ eᴬ F ≡ Π A F

Adequate-sum : ∀ {A} → Sum A → ★₁
Adequate-sum {A} sumᴬ = ∀ f → Fin (sumᴬ f) ≡ Σ A (Fin ∘ f)

Adequate-product : ∀ {A} → Product A → ★₁
Adequate-product {A} productᴬ = ∀ f → Fin (productᴬ f) ≡ Π A (Fin ∘ f)

Adequate-any : ∀ {A} (any : BigOp 𝟚 A) → ★₀
Adequate-any {A} anyᴬ = ∀ f → ✓ (anyᴬ f) ↔ Σ A (✓ ∘ f)

Adequate-all : ∀ {A} (all : BigOp 𝟚 A) → ★₀
Adequate-all {A} allᴬ = ∀ f → ✓ (allᴬ f) ↔ Π A (✓ ∘ f)

StableUnder : ∀ {ℓ A} → Explore ℓ A → (A → A) → ★ _
StableUnder explore p = ∀ {M} ε op (f : _ → M) → explore ε op f ≡ explore ε op (f ∘ p)

SumStableUnder : ∀ {A} → Sum A → (A → A) → ★ _
SumStableUnder sum p = ∀ f → sum f ≡ sum (f ∘ p)

CountStableUnder : ∀ {A} → Count A → (A → A) → ★ _
CountStableUnder count p = ∀ f → count f ≡ count (f ∘ p)

SumStableUnderInjection : ∀ {A} → Sum A → ★ _
SumStableUnderInjection sum = ∀ p → Injective p → SumStableUnder sum p

SumInd : ∀ {A} → Sum A → ★₁
SumInd {A} sum = ∀ (P  : Sum A → ★₀)
                   (P0 : P (λ f → 0))
                   (P+ : ∀ {s₀ s₁ : Sum A} → P s₀ → P s₁ → P (λ f → s₀ f + s₁ f))
                   (Pf : ∀ x → P (λ f → f x))
                →  P sum

ExploreMono : ∀ r {ℓ A} → Explore ℓ A → ★ _
ExploreMono r eᴬ = ∀ {C} (_⊆_ : C → C → ★ r)
                     {z₀ z₁} (z₀⊆z₁ : z₀ ⊆ z₁)
                     {_∙_} (∙-mono : _∙_ Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_)
                     {f g} →
                     (∀ x → f x ⊆ g x) → eᴬ z₀ _∙_ f ⊆ eᴬ z₁ _∙_ g


ExploreExtFun : ∀ {A B} → Explore _ (A → B) → ★₁
ExploreExtFun {A}{B} eᴬᴮ = ∀ {M} ε op {f g : (A → B) → M} → (∀ {φ ψ} → φ ≗ ψ → f φ ≡ g ψ) → eᴬᴮ ε op f ≡ eᴬᴮ ε op g

ExploreMonExt : ∀ r {ℓ A} → Explore ℓ A → ★ _
ExploreMonExt r {ℓ} exploreᴬ =
  ∀ (m : Monoid ℓ r) {f g}
  → let open Mon m
        explore = exploreᴬ ε _∙_
    in
    f ≈° g → explore f ≈ explore g

                         {-
ExploreSgExt : ∀ r {ℓ A} → ExploreNE ℓ A → ★ _
ExploreSgExt r {ℓ} eᴬ = ∀ (sg : Semigroup ℓ r) {f g}
                       → let open Sgrp sg in
                         f ≈° g → eᴬ _∙_ f ≈ eᴬ _∙_ g
                         -}

ExploreExt : ∀ {ℓ A} → Explore ℓ A → ★ _
ExploreExt {ℓ} {A} eᴬ = ∀ {M} ε op {f g : A → M} → f ≗ g → eᴬ ε op f ≡ eᴬ ε op g

SumExt : ∀ {A} → Sum A → ★ _
SumExt sumᴬ = ∀ {f g} → f ≗ g → sumᴬ f ≡ sumᴬ g

CountExt : ∀ {A} → Count A → ★ _
CountExt countᴬ = ∀ {f g} → f ≗ g → countᴬ f ≡ countᴬ g

Exploreε : ∀ ℓ r {A} → Explore _ A → ★ _
Exploreε ℓ r eᴬ = ∀ (m : Monoid ℓ r) →
                       let open Mon m in
                       eᴬ ε _∙_ (const ε) ≈ ε

SumZero : ∀ {A} → Sum A → ★ _
SumZero sumᴬ = sumᴬ (λ _ → 0) ≡ 0

ExploreLinˡ : ∀ ℓ r {A} → Explore _ A → ★ _
ExploreLinˡ ℓ r eᴬ = ∀ m _◎_ f k →
                     let open Mon {ℓ} {r} m
                         open FP _≈_ in
                     k ◎ ε ≈ ε →
                     _◎_ DistributesOverˡ _∙_ →
                     eᴬ ε _∙_ (λ x → k ◎ f x) ≈ k ◎ eᴬ ε _∙_ f

ExploreLinʳ : ∀ ℓ r {A} → Explore _ A → ★ _
ExploreLinʳ ℓ r eᴬ =
  ∀ m _◎_ f k →
    let open Mon {ℓ} {r} m
        open FP _≈_ in
    ε ◎ k ≈ ε →
    _◎_ DistributesOverʳ _∙_ →
    eᴬ ε _∙_ (λ x → f x ◎ k) ≈ eᴬ ε _∙_ f ◎ k

SumLin : ∀ {A} → Sum A → ★ _
SumLin sumᴬ = ∀ f k → sumᴬ (λ x → k * f x) ≡ k * sumᴬ f

{-
ExploreSgHom : ∀ r {ℓ A} → ExploreNE ℓ A → ★ _
ExploreSgHom r eᴬ = ∀ sg f g → let open Sgrp {_} {r} sg in
                            eᴬ _∙_ (f ∙° g) ≈ eᴬ _∙_ f ∙ eᴬ _∙_ g
                            -}

ExploreHom : ∀ ℓ r {A} → Explore _ A → ★ _
ExploreHom ℓ r eᴬ =
  ∀ cm f g →
    let open CMon {ℓ} {r} cm in
    eᴬ ε _∙_ (f ∙° g) ≈ eᴬ ε _∙_ f ∙ eᴬ ε _∙_ g

SumHom : ∀ {A} → Sum A → ★ _
SumHom sumᴬ = ∀ f g → sumᴬ (λ x → f x + g x) ≡ sumᴬ f + sumᴬ g

SumMono : ∀ {A} → Sum A → ★ _
SumMono sumᴬ = ∀ {f g} → (∀ x → f x ≤ g x) → sumᴬ f ≤ sumᴬ g

SumConst : ∀ {A} → Sum A → ★ _
SumConst sumᴬ = ∀ x → sumᴬ (const x) ≡ sumᴬ (const 1) * x

ExploreSwap : ∀ r {ℓ A} → Explore ℓ A → ★ _
ExploreSwap r {ℓ} {A} eᴬ = ∀ {B : ★₀} mon →
                             let open Mon {_} {r} mon in
                           ∀ {eᴮ : (B → C) → C}
                             (eᴮ-ε : eᴮ (const ε) ≈ ε)
                             (hom : ∀ f g → eᴮ (f ∙° g) ≈ eᴮ f ∙ eᴮ g)
                             f
                           → eᴬ ε _∙_ (eᴮ ∘ f) ≈ eᴮ (eᴬ ε _∙_ ∘ flip f)

SumSwap : ∀ {A} → Sum A → ★ _
SumSwap {A} sᴬ = ∀ {B : ★₀}
                   {sᴮ : Sum B}
                   (sᴮ-0 : sᴮ (const 0) ≡ 0)
                   (hom : ∀ f g → sᴮ (f +° g) ≡ sᴮ f + sᴮ g)
                   f
                 → sᴬ (sᴮ ∘ f) ≡ sᴮ (sᴬ ∘ flip f)

Unique : ∀ {A} → Cmp A → Count A → ★ _
Unique cmp count = ∀ x → count (cmp x) ≡ 1
