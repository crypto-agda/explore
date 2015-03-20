{-# OPTIONS --without-K #-}
-- The core properties behind exploration functions
module Explore.Properties where

open import Level.NP using (_⊔_; ₀; ₁; ₛ; Lift)
open import Type using (★₀; ★₁; ★_)
open import Function.NP using (id; _∘′_; _∘_; flip; const; Π; Cmp)
open import Algebra using (Semigroup; module Semigroup; Monoid; module Monoid; CommutativeMonoid; module CommutativeMonoid)
import      Algebra.FunctionProperties.NP
import      Algebra.FunctionProperties.Derived as FPD
open import Algebra.FunctionProperties.Core using (Op₂)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Explicits using (Injective)
open import Data.Nat.NP using (_+_; _*_; _≤_; _+°_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum  using (_⊎_)
open import Data.Zero using (𝟘)
open import Data.One  using (𝟙)
open import Data.Two  using (𝟚; ✓)
open import Data.Fin  using (Fin)
open import Relation.Binary.NP using (module Setoid-Reasoning; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_)

open import Explore.Core

module FP = Algebra.FunctionProperties.NP Π

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
  !_ = sym

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
  ∙-interchange = FPD.FromAssocCommCong.interchange
                    _≈_ isEquivalence
                    _∙_ assoc comm (λ _ → flip ∙-cong refl)

module _ {ℓ a} {A : ★ a} where
    ExploreInd : ∀ p → Explore ℓ A → ★ (a ⊔ ₛ (ℓ ⊔ p))
    ExploreInd p exp =
      ∀ (P  : Explore ℓ A → ★ p)
        (Pε : P empty-explore)
        (P∙ : ∀ {e₀ e₁ : Explore ℓ A} → P e₀ → P e₁ → P (merge-explore e₀ e₁))
        (Pf : ∀ x → P (point-explore x))
      → P exp

    module _ {p} where
        point-explore-ind : (x : A) → ExploreInd p (point-explore x)
        point-explore-ind x _ _ _ Pf = Pf x

        empty-explore-ind : ExploreInd p empty-explore
        empty-explore-ind _ Pε _ _ = Pε

        merge-explore-ind : ∀ {e₀ e₁ : Explore ℓ A}
                            → ExploreInd p e₀ → ExploreInd p e₁
                            → ExploreInd p (merge-explore e₀ e₁)
        merge-explore-ind Pe₀ Pe₁ P Pε _P∙_ Pf = (Pe₀ P Pε _P∙_ Pf) P∙ (Pe₁ P Pε _P∙_ Pf)

    ExploreInd₀ : Explore ℓ A → ★ _
    ExploreInd₀ = ExploreInd ₀

    ExploreInd₁ : Explore ℓ A → ★ _
    ExploreInd₁ = ExploreInd ₁

    BigOpMonInd : ∀ p {c} (M : Monoid c ℓ) → BigOpMon M A → ★ _
    BigOpMonInd p {c} M exp =
      ∀ (P  : BigOpMon M A → ★ p)
        (Pε : P (const ε))
        (P∙ : ∀ {e₀ e₁ : BigOpMon M A} → P e₀ → P e₁ → P (λ f → e₀ f ∙ e₁ f))
        (Pf : ∀ x → P (λ f → f x))
        (P≈ : ∀ {e e'} → e ≈° e' → P e → P e')
      → P exp
      where open Mon M

    module _ (eᴬ : Explore {a} (ₛ ℓ) A) where
        Πᵉ : (A → ★ ℓ) → ★ ℓ
        Πᵉ = eᴬ (Lift 𝟙) _×_

        Σᵉ : (A → ★ ℓ) → ★ ℓ
        Σᵉ = eᴬ (Lift 𝟘) _⊎_

module _ {ℓ a} {A : ★ a} where
    module _ (eᴬ : Explore (ₛ ℓ) A) where
        Lookup : ★ (ₛ ℓ ⊔ a)
        Lookup = ∀ {P : A → ★ ℓ} → Πᵉ eᴬ P → Π A P

        -- alternative name suggestion: tabulate
        Reify : ★ (a ⊔ ₛ ℓ)
        Reify = ∀ {P : A → ★ ℓ} → Π A P → Πᵉ eᴬ P

        Unfocus : ★ (a ⊔ ₛ ℓ)
        Unfocus = ∀ {P : A → ★ ℓ} → Σᵉ eᴬ P → Σ A P

        -- alternative name suggestion: inject
        Focus : ★ (a ⊔ ₛ ℓ)
        Focus = ∀ {P : A → ★ ℓ} → Σ A P → Σᵉ eᴬ P

    Adequate-Σ : ((A → ★ ℓ) → ★ _) → ★ _
    Adequate-Σ Σᴬ = ∀ F → Σᴬ F ≡ Σ A F

    Adequate-Π : ((A → ★ ℓ) → ★ _) → ★ _
    Adequate-Π Πᴬ = ∀ F → Πᴬ F ≡ Π A F

-- This module could be parameterised by the relation on types, here _≡_
module Universal-Adequacy {ℓu ℓe ℓr ℓa}
                          (U : ★_ ℓu)(El : U → ★_ ℓe)
                          (_≈_ : ★_ ℓe → ★_ (ℓa ⊔ ℓe) → ★_ ℓr){A : ★_ ℓa} where
    Adequate-univ-sum : ((A → U) → U) → ★_ (ℓa ⊔ (ℓr ⊔ ℓu))
    Adequate-univ-sum sumᴬ = ∀ f → El (sumᴬ f) ≈ Σ A (El ∘ f)

    Adequate-univ-product : ((A → U) → U) → ★_ (ℓa ⊔ (ℓr ⊔ ℓu))
    Adequate-univ-product productᴬ = ∀ f → El (productᴬ f) ≈ Π A (El ∘ f)

module Adequacy {ℓr}(_≈_ : ★₀ → ★₀ → ★_ ℓr){A : ★₀} where

    -- Universal-Adequacy.Adequate-univ-sum ℕ Fin _≡_
    Adequate-sum : Sum A → ★_ ℓr
    Adequate-sum sumᴬ = ∀ f → Fin (sumᴬ f) ≈ Σ A (Fin ∘ f)

    -- Universal-Adequacy.Adequate-univ-product ℕ Fin _≡_
    Adequate-product : Product A → ★_ ℓr
    Adequate-product productᴬ = ∀ f → Fin (productᴬ f) ≈ Π A (Fin ∘ f)

    -- Universal-Adequacy.Adequate-univ-product 𝟚 ✓ _≡_
    Adequate-any : (any : BigOp 𝟚 A) → ★_ ℓr
    Adequate-any anyᴬ = ∀ f → ✓ (anyᴬ f) ≈ Σ A (✓ ∘ f)

    -- Universal-Adequacy.Adequate-univ-product 𝟚 ✓ _≡_
    Adequate-all : (all : BigOp 𝟚 A) → ★_ ℓr
    Adequate-all allᴬ = ∀ f → ✓ (allᴬ f) ≈ Π A (✓ ∘ f)

module _ {m a}{M : ★ m}{A : ★ a}([⊕] : BigOp M A) where
    BigOpStableUnder : (p : A → A) → ★ _
    BigOpStableUnder p = ∀ f → [⊕] f ≡ [⊕] (f ∘ p)

    -- Extensionality of a big-operator
    BigOp= : ★ _
    BigOp= = {f g : A → M} → f ≗ g → [⊕] f ≡ [⊕] g

module _ {ℓ a} {A : ★ a} (eᴬ : Explore ℓ A) where
    StableUnder : (A → A) → ★ _
    StableUnder p = ∀ {M}(ε : M) op → BigOpStableUnder (eᴬ ε op) p

    -- Extensionality of an exploration function
    Explore= : ★ _
    Explore= = ∀ {M}(ε : M) op → BigOp= (eᴬ ε op)
    ExploreExt = Explore=

module _ {ℓ a} {A : ★ a} r (eᴬ : Explore ℓ A) where
    ExploreMono : ★ _
    ExploreMono = ∀ {C} (_⊆_ : C → C → ★ r)
                    {z₀ z₁} (z₀⊆z₁ : z₀ ⊆ z₁)
                    {_∙_} (∙-mono : _∙_ Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_)
                    {f g} →
                    (∀ x → f x ⊆ g x) → eᴬ z₀ _∙_ f ⊆ eᴬ z₁ _∙_ g

    ExploreMonExt : ★ _
    ExploreMonExt =
      ∀ (m : Monoid ℓ r) {f g}
      → let open Mon m
            bigop = eᴬ ε _∙_
        in
        f ≈° g → bigop f ≈ bigop g

    Exploreε : ★ _
    Exploreε = ∀ (m : Monoid ℓ r) →
                 let open Mon m in
                 eᴬ ε _∙_ (const ε) ≈ ε

    ExploreLinˡ : ★ _
    ExploreLinˡ =
      ∀ m _◎_ f k →
        let open Mon {ℓ} {r} m
            open FP _≈_ in
        k ◎ ε ≈ ε →
        _◎_ DistributesOverˡ _∙_ →
        eᴬ ε _∙_ (λ x → k ◎ f x) ≈ k ◎ eᴬ ε _∙_ f

    ExploreLinʳ : ★ _
    ExploreLinʳ =
      ∀ m _◎_ f k →
        let open Mon {ℓ} {r} m
            open FP _≈_ in
        ε ◎ k ≈ ε →
        _◎_ DistributesOverʳ _∙_ →
        eᴬ ε _∙_ (λ x → f x ◎ k) ≈ eᴬ ε _∙_ f ◎ k

    ExploreHom : ★ _
    ExploreHom =
      ∀ cm f g →
        let open CMon {ℓ} {r} cm in
        eᴬ ε _∙_ (f ∙° g) ≈ eᴬ ε _∙_ f ∙ eᴬ ε _∙_ g

        {-
    ExploreSwap'' : ∀ {b} → ★ _
    ExploreSwap'' {b}
                = ∀ (monM : Monoid _) (monN : Monoid _) →
                    let module M = Mon {_} {r} monM in
                    let module N = Mon {_} {r} monN in
                  ∀ {h : M.C → N.C}
                    (h-ε : h M.ε ≈ N.ε)
                    (h-∙ : ∀ x y → h (x M.∙ y) ≈ h x N.∙ h y)
                    f
                  → eᴬ ε _∙_ (h ∘ f) ≈ h (eᴬ ε _∙_ f)
-}

-- derived from lift-hom with the source monoid being (a → m)
    ExploreSwap : ∀ {b} → ★ _
    ExploreSwap {b}
                = ∀ {B : ★ b} mon →
                    let open Mon {_} {r} mon in
                  ∀ {opᴮ : (B → C) → C}
                    (opᴮ-ε : opᴮ (const ε) ≈ ε)
                    (hom : ∀ f g → opᴮ (f ∙° g) ≈ opᴮ f ∙ opᴮ g)
                    f
                  → eᴬ ε _∙_ (opᴮ ∘ f) ≈ opᴮ (eᴬ ε _∙_ ∘ flip f)

module _ {a} {A : ★ a} (sumᴬ : Sum A) where
    SumStableUnder : (A → A) → ★ _
    SumStableUnder p = ∀ f → sumᴬ f ≡ sumᴬ (f ∘ p)

    SumStableUnderInjection : ★ _
    SumStableUnderInjection = ∀ p → Injective p → SumStableUnder p

    SumInd : ★(₁ ⊔ a)
    SumInd = ∀ (P  : Sum A → ★₀)
               (P0 : P (λ f → 0))
               (P+ : ∀ {s₀ s₁ : Sum A} → P s₀ → P s₁ → P (λ f → s₀ f + s₁ f))
               (Pf : ∀ x → P (λ f → f x))
             → P sumᴬ

    SumExt : ★ _
    SumExt = ∀ {f g} → f ≗ g → sumᴬ f ≡ sumᴬ g

    SumZero : ★ _
    SumZero = sumᴬ (λ _ → 0) ≡ 0

    SumLin : ★ _
    SumLin = ∀ f k → sumᴬ (λ x → k * f x) ≡ k * sumᴬ f

    SumHom : ★ _
    SumHom = ∀ f g → sumᴬ (λ x → f x + g x) ≡ sumᴬ f + sumᴬ g

    SumMono : ★ _
    SumMono = ∀ {f g} → (∀ x → f x ≤ g x) → sumᴬ f ≤ sumᴬ g

    SumConst : ★ _
    SumConst = ∀ x → sumᴬ (const x) ≡ sumᴬ (const 1) * x

    SumSwap : ★ _
    SumSwap = ∀ {B : ★₀}
                {sumᴮ : Sum B}
                (sumᴮ-0 : sumᴮ (const 0) ≡ 0)
                (hom : ∀ f g → sumᴮ (f +° g) ≡ sumᴮ f + sumᴮ g)
                f
              → sumᴬ (sumᴮ ∘ f) ≡ sumᴮ (sumᴬ ∘ flip f)

module _ {a} {A : ★ a} (countᴬ : Count A) where
    CountStableUnder : (A → A) → ★ _
    CountStableUnder p = ∀ f → countᴬ f ≡ countᴬ (f ∘ p)

    CountExt : ★ _
    CountExt = ∀ {f g} → f ≗ g → countᴬ f ≡ countᴬ g

    Unique : Cmp A → ★ _
    Unique cmp = ∀ x → countᴬ (cmp x) ≡ 1
-- -}
-- -}
-- -}
-- -}
