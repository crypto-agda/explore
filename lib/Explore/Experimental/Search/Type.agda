module Search.Type where

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
open import Data.Bool.NP using (Bool; ✓)
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

Search : ∀ ℓ → ★₀ → ★ ₛ ℓ
Search ℓ A = ∀ {M : ★ ℓ} → (_∙_ : M → M → M) → (A → M) → M

Search₀ : ★₀ → ★₁
Search₀ = Search _

Search₁ : ★₀ → ★₂
Search₁ = Search _

[Search] : ([★₀] [→] [★₁]) (Search _)
[Search] Aₚ = ∀⟨ Mₚ ∶ [★₀] ⟩[→] [Op₂] Mₚ [→] (Aₚ [→] Mₚ) [→] Mₚ

⟦Search⟧ : (⟦★₀⟧ ⟦→⟧ ⟦★₁⟧) (Search _) (Search _)
⟦Search⟧ Aᵣ = ∀⟨ Mᵣ ∶ ⟦★₀⟧ ⟩⟦→⟧ ⟦Op₂⟧ Mᵣ ⟦→⟧ (Aᵣ ⟦→⟧ Mᵣ) ⟦→⟧ Mᵣ

⟦Search⟧ᵤ : ∀ {ℓ} → (⟦★₀⟧ ⟦→⟧ ⟦★⟧ (ₛ ℓ)) (Search ℓ) (Search ℓ)
⟦Search⟧ᵤ {ℓ} Aᵣ = ∀⟨ Mᵣ ∶ ⟦★⟧ ℓ ⟩⟦→⟧ ⟦Op₂⟧ Mᵣ ⟦→⟧ (Aᵣ ⟦→⟧ Mᵣ) ⟦→⟧ Mᵣ

-- Trimmed down version of ⟦Search⟧
⟦Search⟧₁ : ∀ {A : ★_ _} (Aᵣ : A → A → ★_ _) → Search _ A → ★₁
⟦Search⟧₁ Aᵣ s = ⟦Search⟧ Aᵣ s s

_∙-search_ : ∀ {ℓ A} → Search ℓ A → Search ℓ A → Search ℓ A
(s₀ ∙-search s₁) _∙_ f = s₀ _∙_ f ∙ s₁ _∙_ f

const-search : ∀ {ℓ A} → A → Search ℓ A
const-search x _ f = f x

SearchInd : ∀ p {ℓ A} → Search ℓ A → ★ _
SearchInd p {ℓ} {A} srch =
  ∀ (P  : Search ℓ A → ★ p)
    (P∙ : ∀ {s₀ s₁ : Search ℓ A} → P s₀ → P s₁ → P (λ _∙_ f → s₀ _∙_ f ∙ s₁ _∙_ f))
    (Pf : ∀ x → P (λ _ f → f x))
  → P srch

const-search-ind : ∀ {ℓ p A} (x : A) → SearchInd p (const-search {ℓ} x)
const-search-ind x _ _ Pf = Pf x

{-
_∙SearchInd_ : ∀ {ℓ p A} {s₀ s₁ : Search ℓ A}
               → SearchInd p s₀ → SearchInd p s₁
               → SearchInd p (s₀ ∙Search s₁)
_∙SearchInd_ {s₀ = s₀} {s₁} Ps₀ Ps₁ P P∙ Pf = Ps₀ (λ s → P s₁ → P (s ∙Search s₁)) (λ {s₂} {s₃} Ps₂ Ps₃ Ps₁' → {!!}) (P∙ ∘ Pf) (Ps₁ P P∙ Pf)
-}

record SearchIndKit p {ℓ A} (P : Search ℓ A → ★ p) : ★ (ₛ ℓ ⊔ p) where
  constructor _,_
  field
    P∙ : ∀ {s₀ s₁ : Search ℓ A} → P s₀ → P s₁ → P (s₀ ∙-search s₁)
    Pf : ∀ x → P (const-search x)

_$kit_ : ∀ {p ℓ A} {P : Search ℓ A → ★ p} {s : Search ℓ A}
         → SearchInd p s → SearchIndKit p P → P s
_$kit_ {P = P} ind (P∙ , Pf) = ind P P∙ Pf

SearchInd₀ : ∀ {ℓ A} → Search ℓ A → ★ _
SearchInd₀ = SearchInd ₀

SearchMon : ∀ {c ℓ} → Monoid c ℓ → ★₀ → ★ _
SearchMon M A = (A → C) → C
  where open Mon M

SearchMonInd : ∀ p {c ℓ} {A} (M : Monoid c ℓ) → SearchMon M A → ★ _
SearchMonInd p {c} {ℓ} {A} M srch =
  ∀ (P  : SearchMon M A → ★ p)
    (P∙ : ∀ {s₀ s₁ : SearchMon M A} → P s₀ → P s₁ → P (λ f → s₀ f ∙ s₁ f))
    (Pf : ∀ x → P (λ f → f x))
    (P≈ : ∀ {s s'} → s ≈° s' → P s → P s')
  → P srch
  where open Mon M

search∘FromSearch : ∀ {m A} → Search m A
                    → ∀ {M : ★ m} → (M → M → M) → (A → M) → (M → M)
search∘FromSearch search op f = search _∘′_ (op ∘ f)

SearchPlug : ∀ {m ℓ A} (M : Monoid m ℓ) (s : Search _ A) → ★ _
SearchPlug M s = ∀ f x → s∘ _∙_ f ε ∙ x ≈ s∘ _∙_ f x
   where open Mon M
         s∘ = search∘FromSearch s

  {-
SearchMon : ∀ m → ★₀ → ★ _
SearchMon m A = ∀ {M : ★ m} → M × Op₂ M → (A → M) → M

SearchMonInd : ∀ p {ℓ} {A} → SearchMon ℓ A → ★ _
SearchMonInd p {ℓ} {A} srch =
  ∀ (P  : SearchMon _ A → ★ p)
    (P∙ : ∀ {s₀ s₁ : SearchMon _ A} → P s₀ → P s₁ → P (λ M f → let _∙_ = proj₂ M in
                                                               s₀ M f ∙ s₁ M f))
    (Pf : ∀ x → P (λ _ f → f x))
  → P srch

searchMonFromSearch : ∀ {ℓ A}
                      → Search ℓ A → SearchMon ℓ A
searchMonFromSearch s = s ∘ proj₂
  -}

searchMonFromSearch : ∀ {c ℓ A}
                      → Search c A → (M : Monoid c ℓ) → SearchMon M A
searchMonFromSearch s M = s _∙_ where open Mon M

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
FindKey A = (A → Bool) →? A

_,-kit_ : ∀ {m p A} {P : Search m A → ★ p}{Q : Search m A → ★ p}
          → SearchIndKit p P → SearchIndKit p Q → SearchIndKit p (P ×° Q)
Pk ,-kit Qk = (λ x y → P∙ Pk (proj₁ x) (proj₁ y) , P∙ Qk (proj₂ x) (proj₂ y))
            , (λ x → Pf Pk x , Pf Qk x)
             where open SearchIndKit

SearchInd-Extra : ∀ p {m A} → Search m A → ★ _
SearchInd-Extra p {m} {A} srch =
  ∀ (Q     : Search m A → ★ p)
    (Q-kit : SearchIndKit p Q)
    (P     : Search m A → ★ p)
    (P∙    : ∀ {s₀ s₁ : Search m A} → Q s₀ → Q s₁ → P s₀ → P s₁
             → P (s₀ ∙-search s₁))
    (Pf    : ∀ x → P (const-search x))
  → P srch

to-extra : ∀ {p m A} {s : Search m A} → SearchInd p s → SearchInd-Extra p s
to-extra s-ind Q Q-kit P P∙ Pf =
 proj₂ (s-ind (Q ×° P)
         (λ { (a , b) (c , d) → Q∙ a c , P∙ a c b d })
         (λ x → Qf x , Pf x))
 where open SearchIndKit Q-kit renaming (P∙ to Q∙; Pf to Qf)

StableUnder : ∀ {ℓ A} → Search ℓ A → (A → A) → ★ _
StableUnder search p = ∀ {M} op (f : _ → M) → search op f ≡ search op (f ∘ p)

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

SearchMono : ∀ r {ℓ A} → Search ℓ A → ★ _
SearchMono r sᴬ = ∀ {C} (_⊆_ : C → C → ★ r)
                    {_∙_} (∙-mono : _∙_ Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_)
                    {f g} →
                    (∀ x → f x ⊆ g x) → sᴬ _∙_ f ⊆ sᴬ _∙_ g


SearchExtFun : ∀ {A B} → Search _ (A → B) → ★₁
SearchExtFun {A}{B} sᴬᴮ = ∀ {M} op {f g : (A → B) → M} → (∀ {φ ψ} → φ ≗ ψ → f φ ≡ g ψ) → sᴬᴮ op f ≡ sᴬᴮ op g

SearchSgExt : ∀ r {ℓ A} → Search ℓ A → ★ _
SearchSgExt r {ℓ} sᴬ = ∀ (sg : Semigroup ℓ r) {f g}
                       → let open Sgrp sg in
                         f ≈° g → sᴬ _∙_ f ≈ sᴬ _∙_ g

SearchExt : ∀ {ℓ A} → Search ℓ A → ★ _
SearchExt {ℓ} {A} sᴬ = ∀ {M} op {f g : A → M} → f ≗ g → sᴬ op f ≡ sᴬ op g

SumExt : ∀ {A} → Sum A → ★ _
SumExt sumᴬ = ∀ {f g} → f ≗ g → sumᴬ f ≡ sumᴬ g

CountExt : ∀ {A} → Count A → ★ _
CountExt countᴬ = ∀ {f g} → f ≗ g → countᴬ f ≡ countᴬ g

Searchε : ∀ ℓ r {A} → Search _ A → ★ _
Searchε ℓ r sᴬ = ∀ (m : Monoid ℓ r) →
                       let open Mon m in
                       sᴬ _∙_ (const ε) ≈ ε

SumZero : ∀ {A} → Sum A → ★ _
SumZero sumᴬ = sumᴬ (λ _ → 0) ≡ 0

SearchLinˡ : ∀ ℓ r {A} → Search _ A → ★ _
SearchLinˡ ℓ r sᴬ = ∀ m _◎_ f k →
                     let open Mon {ℓ} {r} m
                         open FP _≈_ in
                     _◎_ DistributesOverˡ _∙_ →
                     sᴬ _∙_ (λ x → k ◎ f x) ≈ k ◎ sᴬ _∙_ f

SearchLinʳ : ∀ ℓ r {A} → Search _ A → ★ _
SearchLinʳ ℓ r sᴬ =
  ∀ m _◎_ f k →
    let open Mon {ℓ} {r} m
        open FP _≈_ in
    _◎_ DistributesOverʳ _∙_ →
    sᴬ _∙_ (λ x → f x ◎ k) ≈ sᴬ _∙_ f ◎ k

SumLin : ∀ {A} → Sum A → ★ _
SumLin sumᴬ = ∀ f k → sumᴬ (λ x → k * f x) ≡ k * sumᴬ f

SearchHom : ∀ r {ℓ A} → Search ℓ A → ★ _
SearchHom r sᴬ = ∀ sg f g → let open Sgrp {_} {r} sg in
                            sᴬ _∙_ (f ∙° g) ≈ sᴬ _∙_ f ∙ sᴬ _∙_ g

SearchMonHom : ∀ ℓ r {A} → Search _ A → ★ _
SearchMonHom ℓ r sᴬ =
  ∀ cm f g →
    let open CMon {ℓ} {r} cm in
    sᴬ _∙_ (f ∙° g) ≈ sᴬ _∙_ f ∙ sᴬ _∙_ g

SumHom : ∀ {A} → Sum A → ★ _
SumHom sumᴬ = ∀ f g → sumᴬ (λ x → f x + g x) ≡ sumᴬ f + sumᴬ g

SumMono : ∀ {A} → Sum A → ★ _
SumMono sumᴬ = ∀ {f g} → (∀ x → f x ≤ g x) → sumᴬ f ≤ sumᴬ g

SearchSwap : ∀ r {ℓ A} → Search ℓ A → ★ _
SearchSwap r {ℓ} {A} sᴬ = ∀ {B : ★₀} sg f →
                            let open Sgrp {_} {r} sg in
                          ∀ {sᴮ : (B → C) → C}
                          → (hom : ∀ f g → sᴮ (f ∙° g) ≈ sᴮ f ∙ sᴮ g)
                          → sᴬ _∙_ (sᴮ ∘ f) ≈ sᴮ (sᴬ _∙_ ∘ flip f)

Unique : ∀ {A} → Cmp A → Count A → ★ _
Unique cmp count = ∀ x → count (cmp x) ≡ 1

DataΠ : ∀ {b A} → Search _ A → (A → ★ b) → ★ b
DataΠ sA = sA _×_

Lookup : ∀ {b A} → Search _ A → ★ _
Lookup {b} {A} sA = ∀ {B : A → ★ b} → DataΠ sA B → Π A B

Reify : ∀ {b A} → Search _ A → ★ _
Reify {b} {A} sA = ∀ {B : A → ★ b} → Π A B → DataΠ sA B

Reified : ∀ {b A} → Search _ A → ★ _
Reified {b} {A} sA = ∀ {B : A → ★ b} → Π A B ↔ DataΠ sA B

ΣPoint : ∀ {b A} → Search _ A → (A → ★ b) → ★ b
ΣPoint sA = sA _⊎_

Unfocus : ∀ {b A} → Search _ A → ★ _
Unfocus {b} {A} sA = ∀ {B : A → ★ b} → ΣPoint sA B → Σ A B

Focus : ∀ {b A} → Search _ A → ★ _
Focus {b} {A} sA = ∀ {B : A → ★ b} → Σ A B → ΣPoint sA B

Focused : ∀ {b A} → Search _ A → ★ _
Focused {b} {A} sA = ∀ {B : A → ★ b} → Σ A B ↔ ΣPoint sA B
-- -}
