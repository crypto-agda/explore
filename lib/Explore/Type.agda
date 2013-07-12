{-# OPTIONS --without-K #-}
-- The core types behind exploration functions
module Explore.Type where

open import Level using (_⊔_) renaming (zero to ₀; suc to ₛ)
open import Type hiding (★)
open import Function.NP
open import Function.Inverse using (_↔_)
open import Data.Nat.NP hiding (_⊔_)
open import Data.Bit
open import Data.Bits
open import Data.Indexed
open import Algebra
open import Relation.Binary.NP
open import Data.Product
open import Data.Sum
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
Explore ℓ A = ∀ {M : ★ ℓ} → (_∙_ : M → M → M) → (A → M) → M

Explore₀ : ★₀ → ★₁
Explore₀ = Explore _

Explore₁ : ★₀ → ★₂
Explore₁ = Explore _

[Explore] : ([★₀] [→] [★₁]) (Explore _)
[Explore] Aₚ = ∀⟨ Mₚ ∶ [★₀] ⟩[→] [Op₂] Mₚ [→] (Aₚ [→] Mₚ) [→] Mₚ

⟦Explore⟧ : (⟦★₀⟧ ⟦→⟧ ⟦★₁⟧) (Explore _) (Explore _)
⟦Explore⟧ Aᵣ = ∀⟨ Mᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ ⟦Op₂⟧ Mᵣ ⟦→⟧ (Aᵣ ⟦→⟧ Mᵣ) ⟦→⟧ Mᵣ

⟦Explore⟧ᵤ : ∀ {ℓ} → (⟦★₀⟧ ⟦→⟧ ⟦★⟧ (ₛ ℓ)) (Explore ℓ) (Explore ℓ)
⟦Explore⟧ᵤ {ℓ} Aᵣ = ∀⟨ Mᵣ ∶ ⟦★⟧ ℓ ⟩⟦→⟧ ⟦Op₂⟧ Mᵣ ⟦→⟧ (Aᵣ ⟦→⟧ Mᵣ) ⟦→⟧ Mᵣ

-- Trimmed down version of ⟦Explore⟧
⟦Explore⟧₁ : ∀ {A : ★_ _} (Aᵣ : A → A → ★_ _) → Explore _ A → ★₁
⟦Explore⟧₁ Aᵣ s = ⟦Explore⟧ Aᵣ s s

_∙-explore_ : ∀ {ℓ A} → Explore ℓ A → Explore ℓ A → Explore ℓ A
(s₀ ∙-explore s₁) _∙_ f = s₀ _∙_ f ∙ s₁ _∙_ f

const-explore : ∀ {ℓ A} → A → Explore ℓ A
const-explore x _ f = f x

ExploreInd : ∀ p {ℓ A} → Explore ℓ A → ★ _
ExploreInd p {ℓ} {A} srch =
  ∀ (P  : Explore ℓ A → ★ p)
    (P∙ : ∀ {s₀ s₁ : Explore ℓ A} → P s₀ → P s₁ → P (λ _∙_ f → s₀ _∙_ f ∙ s₁ _∙_ f))
    (Pf : ∀ x → P (λ _ f → f x))
  → P srch

const-explore-ind : ∀ {ℓ p A} (x : A) → ExploreInd p (const-explore {ℓ} x)
const-explore-ind x _ _ Pf = Pf x

{-
_∙ExploreInd_ : ∀ {ℓ p A} {s₀ s₁ : Explore ℓ A}
               → ExploreInd p s₀ → ExploreInd p s₁
               → ExploreInd p (s₀ ∙Explore s₁)
_∙ExploreInd_ {s₀ = s₀} {s₁} Ps₀ Ps₁ P P∙ Pf = Ps₀ (λ s → P s₁ → P (s ∙Explore s₁)) (λ {s₂} {s₃} Ps₂ Ps₃ Ps₁' → {!!}) (P∙ ∘ Pf) (Ps₁ P P∙ Pf)
-}

record ExploreIndKit p {ℓ A} (P : Explore ℓ A → ★ p) : ★ (ₛ ℓ ⊔ p) where
  constructor _,_
  field
    P∙ : ∀ {s₀ s₁ : Explore ℓ A} → P s₀ → P s₁ → P (s₀ ∙-explore s₁)
    Pf : ∀ x → P (const-explore x)

_$kit_ : ∀ {p ℓ A} {P : Explore ℓ A → ★ p} {s : Explore ℓ A}
         → ExploreInd p s → ExploreIndKit p P → P s
_$kit_ {P = P} ind (P∙ , Pf) = ind P P∙ Pf

ExploreInd₀ : ∀ {ℓ A} → Explore ℓ A → ★ _
ExploreInd₀ = ExploreInd ₀

ExploreMon : ∀ {c ℓ} → Monoid c ℓ → ★₀ → ★ _
ExploreMon M A = (A → C) → C
  where open Mon M

ExploreMonInd : ∀ p {c ℓ} {A} (M : Monoid c ℓ) → ExploreMon M A → ★ _
ExploreMonInd p {c} {ℓ} {A} M srch =
  ∀ (P  : ExploreMon M A → ★ p)
    (P∙ : ∀ {s₀ s₁ : ExploreMon M A} → P s₀ → P s₁ → P (λ f → s₀ f ∙ s₁ f))
    (Pf : ∀ x → P (λ f → f x))
    (P≈ : ∀ {s s'} → s ≈° s' → P s → P s')
  → P srch
  where open Mon M

explore∘FromExplore : ∀ {m A} → Explore m A
                    → ∀ {M : ★ m} → (M → M → M) → (A → M) → (M → M)
explore∘FromExplore explore op f = explore _∘′_ (op ∘ f)

ExplorePlug : ∀ {m ℓ A} (M : Monoid m ℓ) (s : Explore _ A) → ★ _
ExplorePlug M s = ∀ f x → s∘ _∙_ f ε ∙ x ≈ s∘ _∙_ f x
   where open Mon M
         s∘ = explore∘FromExplore s

  {-
ExploreMon : ∀ m → ★₀ → ★ _
ExploreMon m A = ∀ {M : ★ m} → M × Op₂ M → (A → M) → M

ExploreMonInd : ∀ p {ℓ} {A} → ExploreMon ℓ A → ★ _
ExploreMonInd p {ℓ} {A} srch =
  ∀ (P  : ExploreMon _ A → ★ p)
    (P∙ : ∀ {s₀ s₁ : ExploreMon _ A} → P s₀ → P s₁ → P (λ M f → let _∙_ = proj₂ M in
                                                               s₀ M f ∙ s₁ M f))
    (Pf : ∀ x → P (λ _ f → f x))
  → P srch

exploreMonFromExplore : ∀ {ℓ A}
                      → Explore ℓ A → ExploreMon ℓ A
exploreMonFromExplore s = s ∘ proj₂
  -}

exploreMonFromExplore : ∀ {c ℓ A}
                      → Explore c A → (M : Monoid c ℓ) → ExploreMon M A
exploreMonFromExplore s M = s _∙_ where open Mon M

Sum : ★₀ → ★₀
Sum A = (A → ℕ) → ℕ

Product : ★₀ → ★₀
Product A = (A → ℕ) → ℕ

AdequateSum : ∀ {A} → Sum A → ★₀
AdequateSum {A} sumᴬ = ∀ f → Fin (sumᴬ f) ↔ Σ A (Fin ∘ f)

AdequateProduct : ∀ {A} → Product A → ★₀
AdequateProduct {A} productᴬ = ∀ f → Fin (productᴬ f) ↔ Π A (Fin ∘ f)

Count : ★₀ → ★₀
Count A = (A → Bit) → ℕ

Find? : ★₀ → ★₁
Find? A = ∀ {B : ★₀} → (A →? B) →? B

FindKey : ★₀ → ★₀
FindKey A = (A → 𝟚) →? A

_,-kit_ : ∀ {m p A} {P : Explore m A → ★ p}{Q : Explore m A → ★ p}
          → ExploreIndKit p P → ExploreIndKit p Q → ExploreIndKit p (P ×° Q)
Pk ,-kit Qk = (λ x y → P∙ Pk (proj₁ x) (proj₁ y) , P∙ Qk (proj₂ x) (proj₂ y))
            , (λ x → Pf Pk x , Pf Qk x)
             where open ExploreIndKit

ExploreInd-Extra : ∀ p {m A} → Explore m A → ★ _
ExploreInd-Extra p {m} {A} srch =
  ∀ (Q     : Explore m A → ★ p)
    (Q-kit : ExploreIndKit p Q)
    (P     : Explore m A → ★ p)
    (P∙    : ∀ {s₀ s₁ : Explore m A} → Q s₀ → Q s₁ → P s₀ → P s₁
             → P (s₀ ∙-explore s₁))
    (Pf    : ∀ x → P (const-explore x))
  → P srch

to-extra : ∀ {p m A} {s : Explore m A} → ExploreInd p s → ExploreInd-Extra p s
to-extra s-ind Q Q-kit P P∙ Pf =
 proj₂ (s-ind (Q ×° P)
         (λ { (a , b) (c , d) → Q∙ a c , P∙ a c b d })
         (λ x → Qf x , Pf x))
 where open ExploreIndKit Q-kit renaming (P∙ to Q∙; Pf to Qf)

StableUnder : ∀ {ℓ A} → Explore ℓ A → (A → A) → ★ _
StableUnder explore p = ∀ {M} op (f : _ → M) → explore op f ≡ explore op (f ∘ p)

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
                   (P+ : ∀ {s₀ s₁ : Sum A} → P s₀ → P s₁ → P (λ f → s₀ f + s₁ f))
                   (Pf : ∀ x → P (λ f → f x))
                →  P sum

ExploreMono : ∀ r {ℓ A} → Explore ℓ A → ★ _
ExploreMono r sᴬ = ∀ {C} (_⊆_ : C → C → ★ r)
                    {_∙_} (∙-mono : _∙_ Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_)
                    {f g} →
                    (∀ x → f x ⊆ g x) → sᴬ _∙_ f ⊆ sᴬ _∙_ g


ExploreExtFun : ∀ {A B} → Explore _ (A → B) → ★₁
ExploreExtFun {A}{B} sᴬᴮ = ∀ {M} op {f g : (A → B) → M} → (∀ {φ ψ} → φ ≗ ψ → f φ ≡ g ψ) → sᴬᴮ op f ≡ sᴬᴮ op g

ExploreSgExt : ∀ r {ℓ A} → Explore ℓ A → ★ _
ExploreSgExt r {ℓ} sᴬ = ∀ (sg : Semigroup ℓ r) {f g}
                       → let open Sgrp sg in
                         f ≈° g → sᴬ _∙_ f ≈ sᴬ _∙_ g

ExploreExt : ∀ {ℓ A} → Explore ℓ A → ★ _
ExploreExt {ℓ} {A} sᴬ = ∀ {M} op {f g : A → M} → f ≗ g → sᴬ op f ≡ sᴬ op g

SumExt : ∀ {A} → Sum A → ★ _
SumExt sumᴬ = ∀ {f g} → f ≗ g → sumᴬ f ≡ sumᴬ g

CountExt : ∀ {A} → Count A → ★ _
CountExt countᴬ = ∀ {f g} → f ≗ g → countᴬ f ≡ countᴬ g

Exploreε : ∀ ℓ r {A} → Explore _ A → ★ _
Exploreε ℓ r sᴬ = ∀ (m : Monoid ℓ r) →
                       let open Mon m in
                       sᴬ _∙_ (const ε) ≈ ε

SumZero : ∀ {A} → Sum A → ★ _
SumZero sumᴬ = sumᴬ (λ _ → 0) ≡ 0

ExploreLinˡ : ∀ ℓ r {A} → Explore _ A → ★ _
ExploreLinˡ ℓ r sᴬ = ∀ m _◎_ f k →
                     let open Mon {ℓ} {r} m
                         open FP _≈_ in
                     _◎_ DistributesOverˡ _∙_ →
                     sᴬ _∙_ (λ x → k ◎ f x) ≈ k ◎ sᴬ _∙_ f

ExploreLinʳ : ∀ ℓ r {A} → Explore _ A → ★ _
ExploreLinʳ ℓ r sᴬ =
  ∀ m _◎_ f k →
    let open Mon {ℓ} {r} m
        open FP _≈_ in
    _◎_ DistributesOverʳ _∙_ →
    sᴬ _∙_ (λ x → f x ◎ k) ≈ sᴬ _∙_ f ◎ k

SumLin : ∀ {A} → Sum A → ★ _
SumLin sumᴬ = ∀ f k → sumᴬ (λ x → k * f x) ≡ k * sumᴬ f

ExploreHom : ∀ r {ℓ A} → Explore ℓ A → ★ _
ExploreHom r sᴬ = ∀ sg f g → let open Sgrp {_} {r} sg in
                            sᴬ _∙_ (f ∙° g) ≈ sᴬ _∙_ f ∙ sᴬ _∙_ g

ExploreMonHom : ∀ ℓ r {A} → Explore _ A → ★ _
ExploreMonHom ℓ r sᴬ =
  ∀ cm f g →
    let open CMon {ℓ} {r} cm in
    sᴬ _∙_ (f ∙° g) ≈ sᴬ _∙_ f ∙ sᴬ _∙_ g

SumHom : ∀ {A} → Sum A → ★ _
SumHom sumᴬ = ∀ f g → sumᴬ (λ x → f x + g x) ≡ sumᴬ f + sumᴬ g

SumMono : ∀ {A} → Sum A → ★ _
SumMono sumᴬ = ∀ {f g} → (∀ x → f x ≤ g x) → sumᴬ f ≤ sumᴬ g

ExploreSwap : ∀ r {ℓ A} → Explore ℓ A → ★ _
ExploreSwap r {ℓ} {A} sᴬ = ∀ {B : ★₀} sg f →
                            let open Sgrp {_} {r} sg in
                          ∀ {sᴮ : (B → C) → C}
                          → (hom : ∀ f g → sᴮ (f ∙° g) ≈ sᴮ f ∙ sᴮ g)
                          → sᴬ _∙_ (sᴮ ∘ f) ≈ sᴮ (sᴬ _∙_ ∘ flip f)

Unique : ∀ {A} → Cmp A → Count A → ★ _
Unique cmp count = ∀ x → count (cmp x) ≡ 1

DataΠ : ∀ {b A} → Explore _ A → (A → ★ b) → ★ b
DataΠ sA = sA _×_

Lookup : ∀ {b A} → Explore _ A → ★ _
Lookup {b} {A} sA = ∀ {B : A → ★ b} → DataΠ sA B → Π A B

Reify : ∀ {b A} → Explore _ A → ★ _
Reify {b} {A} sA = ∀ {B : A → ★ b} → Π A B → DataΠ sA B

Reified : ∀ {b A} → Explore _ A → ★ _
Reified {b} {A} sA = ∀ {B : A → ★ b} → Π A B ↔ DataΠ sA B

ΣPoint : ∀ {b A} → Explore _ A → (A → ★ b) → ★ b
ΣPoint sA = sA _⊎_

Unfocus : ∀ {b A} → Explore _ A → ★ _
Unfocus {b} {A} sA = ∀ {B : A → ★ b} → ΣPoint sA B → Σ A B

Focus : ∀ {b A} → Explore _ A → ★ _
Focus {b} {A} sA = ∀ {B : A → ★ b} → Σ A B → ΣPoint sA B

Focused : ∀ {b A} → Explore _ A → ★ _
Focused {b} {A} sA = ∀ {B : A → ★ b} → Σ A B ↔ ΣPoint sA B
-- -}
