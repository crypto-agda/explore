{-# OPTIONS --without-K #-}
-- The core types behind exploration functions
module Explore.Type where

open import Level.NP
open import Type hiding (★)
open import Function.NP
open import Function.Inverse using (_↔_)
open import Data.Nat.NP hiding (_⊔_)
open import Data.Indexed
open import Algebra
open import Relation.Binary.NP
open import Data.Product
open import Data.Sum
open import Data.Zero using (𝟘)
open import Data.One using (𝟙)
open import Data.Two using (𝟚; ✓)
open import Data.Maybe.NP using (_→?_)
open import Data.Fin using (Fin)
import Algebra.FunctionProperties.NP as FP
open FP using (Op₂)
open import Relation.Unary.Logical
open import Relation.Binary.Logical
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)

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

Explore : ∀ ℓ → ★₀ → ★ ₛ ℓ
Explore ℓ A = ∀ {M : ★ ℓ} (ε : M) (_∙_ : M → M → M) → (A → M) → M

Explore₀ : ★₀ → ★₁
Explore₀ = Explore _

Explore₁ : ★₀ → ★₂
Explore₁ = Explore _

[Explore] : ([★₀] [→] [★₁]) (Explore _)
[Explore] Aₚ = ∀⟨ Mₚ ∶ [★₀] ⟩[→] Mₚ [→] [Op₂] Mₚ [→] (Aₚ [→] Mₚ) [→] Mₚ

⟦Explore⟧ : (⟦★₀⟧ ⟦→⟧ ⟦★₁⟧) (Explore _) (Explore _)
⟦Explore⟧ Aᵣ = ∀⟨ Mᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ Mᵣ ⟦→⟧ ⟦Op₂⟧ Mᵣ ⟦→⟧ (Aᵣ ⟦→⟧ Mᵣ) ⟦→⟧ Mᵣ

⟦Explore⟧ᵤ : ∀ {ℓ} → (⟦★₀⟧ ⟦→⟧ ⟦★⟧ (ₛ ℓ)) (Explore ℓ) (Explore ℓ)
⟦Explore⟧ᵤ {ℓ} Aᵣ = ∀⟨ Mᵣ ∶ ⟦★⟧ ℓ ⟩⟦→⟧ Mᵣ ⟦→⟧ ⟦Op₂⟧ Mᵣ ⟦→⟧ (Aᵣ ⟦→⟧ Mᵣ) ⟦→⟧ Mᵣ

-- Trimmed down version of ⟦Explore⟧
⟦Explore⟧₁ : ∀ {A : ★_ _} (Aᵣ : A → A → ★_ _) → Explore _ A → ★₁
⟦Explore⟧₁ Aᵣ e = ⟦Explore⟧ Aᵣ e e

-- These three basic combinators are defined here
-- since they are used to define ExploreInd
module _ {ℓ A} where
    merge-explore : Explore ℓ A → Explore ℓ A → Explore ℓ A
    merge-explore e₀ e₁ ε _∙_ f = e₀ ε _∙_ f ∙ e₁ ε _∙_ f

    empty-explore : Explore ℓ A
    empty-explore ε _ _ = ε

    point-explore : A → Explore ℓ A
    point-explore x _ _ f = f x

ExploreInd : ∀ p {ℓ A} → Explore ℓ A → ★ _
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

record ExploreIndKit p {ℓ A} (P : Explore ℓ A → ★ p) : ★ (ₛ ℓ ⊔ p) where
  constructor mk
  field
    Pε : P empty-explore
    P∙ : ∀ {e₀ e₁ : Explore ℓ A} → P e₀ → P e₁ → P (merge-explore e₀ e₁)
    Pf : ∀ x → P (point-explore x)

_$kit_ : ∀ {p ℓ A} {P : Explore ℓ A → ★ p} {e : Explore ℓ A}
         → ExploreInd p e → ExploreIndKit p P → P e
_$kit_ {P = P} ind (mk Pε P∙ Pf) = ind P Pε P∙ Pf

ExploreInd₀ : ∀ {ℓ A} → Explore ℓ A → ★ _
ExploreInd₀ = ExploreInd ₀

ExploreInd₁ : ∀ {ℓ A} → Explore ℓ A → ★ _
ExploreInd₁ = ExploreInd ₁

ExploreMon : ∀ {c ℓ} → Monoid c ℓ → ★₀ → ★ _
ExploreMon M A = (A → C) → C
  where open Mon M

ExploreMonInd : ∀ p {c ℓ} {A} (M : Monoid c ℓ) → ExploreMon M A → ★ _
ExploreMonInd p {c} {ℓ} {A} M exp =
  ∀ (P  : ExploreMon M A → ★ p)
    (Pε : P (const ε))
    (P∙ : ∀ {e₀ e₁ : ExploreMon M A} → P e₀ → P e₁ → P (λ f → e₀ f ∙ e₁ f))
    (Pf : ∀ x → P (λ f → f x))
    (P≈ : ∀ {e e'} → e ≈° e' → P e → P e')
  → P exp
  where open Mon M

  {-
explore∘FromExploreNE : ∀ {m A} → ExploreNE m A → Explore m A
explore∘FromExploreNE explore ε op f = explore _∘′_ (op ∘ f) ε
-}

explore∘FromExplore : ∀ {m A} → Explore m A → Explore m A
explore∘FromExplore explore ε op f = explore id _∘′_ (op ∘ f) ε

ExplorePlug : ∀ {m ℓ A} (M : Monoid m ℓ) (e : Explore _ A) → ★ _
ExplorePlug M e = ∀ f x → e∘ ε _∙_ f ∙ x ≈ e∘ x _∙_ f
   where open Mon M
         e∘ = explore∘FromExplore e

  {-
ExploreMon : ∀ m → ★₀ → ★ _
ExploreMon m A = ∀ {M : ★ m} → M × Op₂ M → (A → M) → M

ExploreMonInd : ∀ p {ℓ} {A} → ExploreMon ℓ A → ★ _
ExploreMonInd p {ℓ} {A} exp =
  ∀ (P  : ExploreMon _ A → ★ p)
    (P∙ : ∀ {e₀ e₁ : ExploreMon _ A} → P e₀ → P e₁ → P (λ M f → let _∙_ = proj₂ M in
                                                               e₀ M f ∙ e₁ M f))
    (Pf : ∀ x → P (λ _ f → f x))
  → P exp

exploreMonFromExplore : ∀ {ℓ A}
                      → Explore ℓ A → ExploreMon ℓ A
exploreMonFromExplore e = e ∘ proj₂
  -}

exploreMonFromExplore : ∀ {c ℓ A}
                      → Explore c A → (M : Monoid c ℓ) → ExploreMon M A
exploreMonFromExplore e M f = e ε _∙_ f where open Mon M

Sum : ★₀ → ★₀
Sum A = (A → ℕ) → ℕ

Product : ★₀ → ★₀
Product A = (A → ℕ) → ℕ

AdequateSum : ∀ {A} → Sum A → ★₀
AdequateSum {A} sumᴬ = ∀ f → Fin (sumᴬ f) ↔ Σ A (Fin ∘ f)

AdequateProduct : ∀ {A} → Product A → ★₀
AdequateProduct {A} productᴬ = ∀ f → Fin (productᴬ f) ↔ Π A (Fin ∘ f)

Count : ★₀ → ★₀
Count A = (A → 𝟚) → ℕ

Find? : ★₀ → ★₁
Find? A = ∀ {B : ★₀} → (A →? B) →? B

FindKey : ★₀ → ★₀
FindKey A = (A → 𝟚) →? A

_,-kit_ : ∀ {m p A} {P : Explore m A → ★ p}{Q : Explore m A → ★ p}
          → ExploreIndKit p P → ExploreIndKit p Q → ExploreIndKit p (P ×° Q)
Pk ,-kit Qk = mk (Pε Pk , Pε Qk)
                 (λ x y → P∙ Pk (proj₁ x) (proj₁ y) , P∙ Qk (proj₂ x) (proj₂ y))
                 (λ x → Pf Pk x , Pf Qk x)
             where open ExploreIndKit

module Extra where
    ExploreInd-Extra : ∀ p {m A} → Explore m A → ★ _
    ExploreInd-Extra p {m} {A} exp =
      ∀ (Q     : Explore m A → ★ p)
        (Q-kit : ExploreIndKit p Q)
        (P     : Explore m A → ★ p)
        (Pε    : P empty-explore)
        (P∙    : ∀ {e₀ e₁ : Explore m A} → Q e₀ → Q e₁ → P e₀ → P e₁
                 → P (merge-explore e₀ e₁))
        (Pf    : ∀ x → P (point-explore x))
      → P exp

    to-extra : ∀ {p m A} {e : Explore m A} → ExploreInd p e → ExploreInd-Extra p e
    to-extra e-ind Q Q-kit P Pε P∙ Pf =
     proj₂ (e-ind (Q ×° P)
             (Qε , Pε)
             (λ { (a , b) (c , d) → Q∙ a c , P∙ a c b d })
             (λ x → Qf x , Pf x))
     where open ExploreIndKit Q-kit renaming (Pε to Qε; P∙ to Q∙; Pf to Qf)

StableUnder : ∀ {ℓ A} → Explore ℓ A → (A → A) → ★ _
StableUnder explore p = ∀ {M} ε op (f : _ → M) → explore ε op f ≡ explore ε op (f ∘ p)

SumStableUnder : ∀ {A} → Sum A → (A → A) → ★ _
SumStableUnder sum p = ∀ f → sum f ≡ sum (f ∘ p)

CountStableUnder : ∀ {A} → Count A → (A → A) → ★ _
CountStableUnder count p = ∀ f → count f ≡ count (f ∘ p)

-- TODO: remove the hard-wired ≡
Injective : ∀ {a b}{A : ★ a}{B : ★ b}(f : A → B) → ★ _
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

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

ExploreSwap : ∀ r {ℓ A} → Explore ℓ A → ★ _
ExploreSwap r {ℓ} {A} eᴬ = ∀ {B : ★₀} mon f →
                            let open Mon {_} {r} mon in
                          ∀ {eᴮ : (B → C) → C}
                            (eᴮ-ε : eᴮ (const ε) ≈ ε)
                            (hom : ∀ f g → eᴮ (f ∙° g) ≈ eᴮ f ∙ eᴮ g)
                          → eᴬ ε _∙_ (eᴮ ∘ f) ≈ eᴮ (eᴬ ε _∙_ ∘ flip f)

Unique : ∀ {A} → Cmp A → Count A → ★ _
Unique cmp count = ∀ x → count (cmp x) ≡ 1

module _ {ℓ A} (eᴬ : Explore (ₛ ℓ) A) where
    DataΠ : (A → ★ ℓ) → ★ ℓ
    DataΠ = eᴬ (Lift 𝟙) _×_

    ΣPoint : (A → ★ ℓ) → ★ ℓ
    ΣPoint = eᴬ (Lift 𝟘) _⊎_

module _ {ℓ A} (eᴬ : Explore (ₛ ℓ) A) where
    Lookup : ★ (ₛ ℓ)
    Lookup = ∀ {P : A → ★ ℓ} → DataΠ eᴬ P → Π A P

    Reify : ★ (ₛ ℓ)
    Reify = ∀ {P : A → ★ ℓ} → Π A P → DataΠ eᴬ P

    Reified : ★ (ₛ ℓ)
    Reified = ∀ {P : A → ★ ℓ} → Π A P ↔ DataΠ eᴬ P

    Unfocus : ★ (ₛ ℓ)
    Unfocus = ∀ {P : A → ★ ℓ} → ΣPoint eᴬ P → Σ A P

    Focus : ★ (ₛ ℓ)
    Focus = ∀ {P : A → ★ ℓ} → Σ A P → ΣPoint eᴬ P

    Focused : ★ (ₛ ℓ)
    Focused = ∀ {P : A → ★ ℓ} → Σ A P ↔ ΣPoint eᴬ P
-- -}
