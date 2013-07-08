import Level as L
open import Type
open import Function
open import Algebra
open import Algebra.FunctionProperties.NP
open import Data.Nat.NP hiding (_^_)
open import Data.Nat.Properties
open import Data.One hiding (_≤_)
open import Data.Sum
open import Data.Maybe.NP
open import Data.Product
open import Data.Bits
open import Data.Zero
open import Data.Bool.NP as Bool
import Function.Equality as FE
open FE using (_⟨$⟩_ ; ≡-setoid)
import Function.Injection as Finj
import Function.Inverse as FI
open FI using (_↔_; module Inverse)
open import Function.LeftInverse using (_RightInverseOf_)
import Function.Related as FR
open import Function.Related.TypeIsomorphisms.NP
open import Relation.Binary.NP
open import Relation.Binary.Sum
open import Relation.Binary.Product.Pointwise
open import Relation.Unary.Logical
open import Relation.Binary.Logical
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_)
open import Search.Type

module sum-setoid where


SearchExtFun-úber : ∀ {A B} → (SF : Search (A → B)) → SearchInd SF → SearchExtFun SF
SearchExtFun-úber sf sf-ind op {f = f}{g} f≈g = sf-ind (λ s → s op f ≡ s op g) (≡.cong₂ op) (λ x → f≈g (λ _ → ≡.refl))

SearchExtFun-úber' : ∀ {A B} → (SF : Search (A → B)) → SearchInd SF → SearchExtFun SF
SearchExtFun-úber' sf sf-ind op {f = f}{g} f≈g = sf-ind (λ s → s op f ≡ s op g) (≡.cong₂ op) (λ x → f≈g (λ _ → ≡.refl))

SearchExtoid : ∀ {A : Setoid L.zero L.zero} → Search (Setoid.Carrier A) → ★₁
SearchExtoid {A} sᴬ = ∀ {M} op {f g : A FE.⟶ ≡.setoid M} → Setoid._≈_ (A FE.⇨ ≡.setoid M) f g →  sᴬ op (_⟨$⟩_ f) ≡ sᴬ op (_⟨$⟩_ g)

sum-lin⇒sum-zero : ∀ {A} → {sum : Sum A} → SumLin sum → SumZero sum
sum-lin⇒sum-zero sum-lin = sum-lin (λ _ → 0) 0

sum-mono⇒sum-ext : ∀ {A} → {sum : Sum A} → SumMono sum → SumExt sum
sum-mono⇒sum-ext sum-mono f≗g = ℕ≤.antisym (sum-mono (ℕ≤.reflexive ∘ f≗g)) (sum-mono (ℕ≤.reflexive ∘ ≡.sym ∘ f≗g))

sum-ext+sum-hom⇒sum-mono : ∀ {A} → {sum : Sum A} → SumExt sum → SumHom sum → SumMono sum
sum-ext+sum-hom⇒sum-mono {sum = sum} sum-ext sum-hom {f} {g} f≤°g =
    sum f                         ≤⟨ m≤m+n _ _ ⟩
    sum f + sum (λ x → g x ∸ f x) ≡⟨ ≡.sym (sum-hom _ _) ⟩
    sum (λ x → f x + (g x ∸ f x)) ≡⟨ sum-ext (m+n∸m≡n ∘ f≤°g) ⟩
    sum g ∎ where open ≤-Reasoning

record SumPropoid (As : Setoid L.zero L.zero) : ★₁ where
  constructor _,_
  module ≈ᴬ = Setoid As
  open ≈ᴬ using () renaming (_≈_ to _≈ᴬ_; Carrier to A)
  field
    search     : Search A
    search-ind : SearchInd search

  ⟦search⟧ : ∀ {Aᵣ : A → A → ★}
               (Aᵣ-refl : Reflexive Aᵣ)
              → ⟦Search⟧₁ Aᵣ search
  ⟦search⟧ Aᵣ-refl Mᵣ ∙ᵣ fᵣ = search-ind (λ s → Mᵣ (s _ _) (s _ _))
                                         (λ η → ∙ᵣ η)
                                         (λ _ → fᵣ Aᵣ-refl)

  -- this one is given for completness but the asking for the Aₚ predicate
  -- to be trivial makes this result useless.
  [search] : ∀ (Aₚ : A → ★)
               (Aₚ-triv : ∀ x → Aₚ x)
             → [Search] Aₚ search
  [search] Aₚ Aₚ-triv {M} Mₚ ∙ₚ fₚ =
    search-ind (λ s → Mₚ (s _ _)) (λ η → ∙ₚ η) (λ x → fₚ (Aₚ-triv x))

  search-sg-ext : SearchSgExt search
  search-sg-ext sg {f} {g} f≈°g = search-ind (λ s → s _ f ≈ s _ g) ∙-cong f≈°g
    where open Sgrp sg

  foo : ∀ {A : ★} {R : A → A → ★} → Reflexive R → _≡_ ⇒ R
  foo R-refl ≡.refl = R-refl

  search-ext : SearchExt search
  -- search-ext op {g = g} pf = ⟦search⟧ {_≡_} ≡.refl _≡_ (λ η → ≡.cong₂ op η) (≡.trans (pf _) ∘ ≡.cong g) -- (foo (λ {x} → pf x))
  search-ext op pf = ⟦search⟧ {_≡_} ≡.refl _≡_ (λ η → ≡.cong₂ op η)
                                               (foo (λ {x} → pf x))
 -- (λ { {x} .{x} ≡.refl → pf _ })
  -- {!search-extoid op = ⟦search⟧ {_≈ᴬ_} ≈ᴬ.refl _≡_ (λ η → ≡.cong₂ op η)!}

  search-mono : SearchMono search
  search-mono _⊆_ _∙-mono_ {f} {g} f⊆°g = search-ind (λ s → s _ f ⊆ s _ g) _∙-mono_ f⊆°g

  search-swap : SearchSwap search
  search-swap sg f {sᴮ} pf = search-ind (λ s → s _ (sᴮ ∘ f) ≈ sᴮ (s _ ∘ flip f)) (λ p q → trans (∙-cong p q) (sym (pf _ _))) (λ _ → refl)
    where open Sgrp sg

  searchMon : SearchMon A
  searchMon m = search _∙_
    where open Mon m

  search-ε : Searchε searchMon
  search-ε m = search-ind (λ s → s _ (const ε) ≈ ε) (λ x≈ε y≈ε → trans (∙-cong x≈ε y≈ε) (proj₁ identity ε)) (λ _ → refl)
    where open Mon m

  search-hom : SearchMonHom searchMon
  search-hom cm f g = search-ind (λ s → s _ (f ∙° g) ≈ s _ f ∙ s _ g)
                                 (λ p₀ p₁ → trans (∙-cong p₀ p₁) (∙-interchange _ _ _ _)) (λ _ → refl)
    where open CMon cm

  search-hom′ :
      ∀ {S T}
        (_+_ : Op₂ S)
        (_*_ : Op₂ T)
        (f   : S → T)
        (g   : A → S)
        (hom : ∀ x y → f (x + y) ≡ f x * f y)
        → f (search _+_ g) ≡ search _*_ (f ∘ g)
  search-hom′ _+_ _*_ f g hom = search-ind (λ s → f (s _+_ g) ≡ s _*_ (f ∘ g))
                                           (λ p q → ≡.trans (hom _ _) (≡.cong₂ _*_ p q))
                                           (λ _ → ≡.refl)

  StableUnder : As FE.⟶ As  → ★₁
  StableUnder p = ∀ {B} (op : Op₂ B) f → search op f ≡ search op (f ∘ _⟨$⟩_ p)

  sum : Sum A
  sum = search _+_

  sum-ind : SumInd sum
  sum-ind P P+ Pf = search-ind (λ s → P (s _+_)) P+ Pf

  sum-ext : SumExt sum
  sum-ext = search-ext _+_

  sum-zero : SumZero sum
  sum-zero = search-ε ℕ+.monoid

  sum-hom : SumHom sum
  sum-hom = search-hom ℕ°.+-commutativeMonoid

  sum-mono : SumMono sum
  sum-mono = search-mono _≤_ _+-mono_

  sum-lin : SumLin sum
  sum-lin f zero    = sum-zero
  sum-lin f (suc k) = ≡.trans (sum-hom f (λ x → k * f x)) (≡.cong₂ _+_ (≡.refl {x = sum f}) (sum-lin f k))

  SumStableUnder : As FE.⟶ As → ★
  SumStableUnder p = ∀ (f : As FE.⟶ ≡.setoid ℕ) → sum (_⟨$⟩_ f) ≡ sum (_⟨$⟩_ (f FE.∘ p))

  sumStableUnder : ∀ {p} → StableUnder p → SumStableUnder p
  sumStableUnder SU-p f = SU-p _+_ (_⟨$⟩_ f)

  Card : ℕ
  Card = sum (const 1)

  count : Count A
  count f = sum (Bool.toℕ ∘ f)

  count-ext : CountExt count
  count-ext f≗g = sum-ext (≡.cong Bool.toℕ ∘ f≗g)

  CountStableUnder : As FE.⟶ As → ★
  CountStableUnder p = ∀ (f : As FE.⟶ ≡.setoid Bool) → count (_⟨$⟩_ f) ≡ count (_⟨$⟩_ (f FE.∘ p))

  countStableUnder : ∀ {p} → SumStableUnder p → CountStableUnder p
  countStableUnder sumSU-p f = sumSU-p (≡.:→-to-Π Bool.toℕ FE.∘ f)

  search-extoid : SearchExtoid {As} search
  -- search-extoid op {f = f}{g} f≈g = search-ind (λ s₁ → s₁ op (_⟨$⟩_ f) ≡ s₁ op (_⟨$⟩_ g)) (≡.cong₂ op) (λ x → f≈g (Setoid.refl As))
  search-extoid op = ⟦search⟧ {_≈ᴬ_} ≈ᴬ.refl _≡_ (λ η → ≡.cong₂ op η)

SumProp : ★ → ★₁
SumProp A = SumPropoid (≡.setoid A)

open SumPropoid public

search-swap' : ∀ {A B} cm (μA : SumPropoid A) (μB : SumPropoid B) f →
               let open CMon cm
                   sᴬ = search μA _∙_
                   sᴮ = search μB _∙_ in
               sᴬ (sᴮ ∘ f) ≈ sᴮ (sᴬ ∘ flip f)
search-swap' cm μA μB f = search-swap μA sg f (search-hom μB cm)
  where open CMon cm

sum-swap : ∀ {A B} (μA : SumPropoid A) (μB : SumPropoid B) f →
           sum μA (sum μB ∘ f) ≡ sum μB (sum μA ∘ flip f)
sum-swap = search-swap' ℕ°.+-commutativeMonoid

_≈Sum_ : ∀ {A} → (sum₀ sum₁ : Sum A) → ★
sum₀ ≈Sum sum₁ = ∀ f → sum₀ f ≡ sum₁ f

_≈Search_ : ∀ {A} → (s₀ s₁ : Search A) → ★₁
s₀ ≈Search s₁ = ∀ {B} (op : Op₂ B) f → s₀ op f ≡ s₁ op f


μ𝟙 : SumProp 𝟙
μ𝟙 = srch , ind
  where
    srch : Search 𝟙
    srch _ f = f _

    ind : SearchInd srch
    ind _ _ Pf = Pf _

μBit : SumProp Bit
μBit = searchBit , ind
  where
    searchBit : Search Bit
    searchBit _∙_ f = f 0b ∙ f 1b

    ind : SearchInd searchBit
    ind _ _P∙_ Pf = Pf 0b P∙ Pf 1b

infixr 4 _+Search_

_+Search_ : ∀ {A B} → Search A → Search B → Search (A ⊎ B)
(searchᴬ +Search searchᴮ) _∙_ f = searchᴬ _∙_ (f ∘ inj₁) ∙ searchᴮ _∙_ (f ∘ inj₂)

_+SearchInd_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B} →
                 SearchInd sᴬ → SearchInd sᴮ → SearchInd (sᴬ +Search sᴮ)
(Psᴬ +SearchInd Psᴮ) P P∙ Pf
  = P∙ (Psᴬ (λ s → P (λ _ f → s _ (f ∘ inj₁))) P∙ (Pf ∘ inj₁))
       (Psᴮ (λ s → P (λ _ f → s _ (f ∘ inj₂))) P∙ (Pf ∘ inj₂))

infixr 4 _+Sum_

_+Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A ⊎ B)
(sumᴬ +Sum sumᴮ) f = sumᴬ (f ∘ inj₁) + sumᴮ (f ∘ inj₂)

_+μ_ : ∀ {A B} → SumPropoid A → SumPropoid B → SumPropoid (A ⊎-setoid B)
μA +μ μB = _ , search-ind μA +SearchInd search-ind μB

infixr 4 _×Search_

-- liftM2 _,_ in the continuation monad
_×Search_ : ∀ {A B} → Search A → Search B → Search (A × B)
(searchᴬ ×Search searchᴮ) op f = searchᴬ op (λ x → searchᴮ op (curry f x))

_×SearchInd_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B}
               → SearchInd sᴬ → SearchInd sᴮ → SearchInd (sᴬ ×Search sᴮ)
(Psᴬ ×SearchInd Psᴮ) P P∙ Pf =
  Psᴬ (λ s → P (λ _ _ → s _ _)) P∙ (Psᴮ (λ s → P (λ _ _ → s _ _)) P∙ ∘ curry Pf)

_×SearchExt_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B} →
              SearchExt sᴬ → SearchExt sᴮ → SearchExt (sᴬ ×Search sᴮ)
(sᴬ-ext ×SearchExt sᴮ-ext) sg f≗g = sᴬ-ext sg (sᴮ-ext sg ∘ curry f≗g)

infixr 4 _×Sum_

-- liftM2 _,_ in the continuation monad
_×Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
(sumᴬ ×Sum sumᴮ) f = sumᴬ (λ x₀ →
                       sumᴮ (λ x₁ →
                         f (x₀ , x₁)))

infixr 4 _×μ_

_×μ_ : ∀ {A B} → SumPropoid A → SumPropoid B → SumPropoid (A ×-setoid B)
μA ×μ μB = _ , search-ind μA ×SearchInd search-ind μB

sum-const : ∀ {A} (μA : SumProp A) → ∀ k → sum μA (const k) ≡ Card μA * k
sum-const μA k
  rewrite ℕ°.*-comm (Card μA) k
        | ≡.sym (sum-lin μA (const 1) k)
        | proj₂ ℕ°.*-identity k = ≡.refl

infixr 4 _×Sum-proj₁_ _×Sum-proj₁'_ _×Sum-proj₂_ _×Sum-proj₂'_

_×Sum-proj₁_ : ∀ {A B}
                 (μA : SumProp A)
                 (μB : SumProp B)
                 f →
                 sum (μA ×μ μB) (f ∘ proj₁) ≡ Card μB * sum μA f
(μA ×Sum-proj₁ μB) f
  rewrite sum-ext μA (sum-const μB ∘ f)
        = sum-lin μA f (Card μB)

_×Sum-proj₂_ : ∀ {A B}
                 (μA : SumProp A)
                 (μB : SumProp B)
                 f →
                 sum (μA ×μ μB) (f ∘ proj₂) ≡ Card μA * sum μB f
(μA ×Sum-proj₂ μB) f = sum-const μA (sum μB f)

_×Sum-proj₁'_ : ∀ {A B}
                  (μA : SumProp A) (μB : SumProp B)
                  {f} {g} →
                  sum μA f ≡ sum μA g →
                  sum (μA ×μ μB) (f ∘ proj₁) ≡ sum (μA ×μ μB) (g ∘ proj₁)
(μA ×Sum-proj₁' μB) {f} {g} sumf≡sumg
  rewrite (μA ×Sum-proj₁ μB) f
        | (μA ×Sum-proj₁ μB) g
        | sumf≡sumg = ≡.refl

_×Sum-proj₂'_ : ∀ {A B}
                  (μA : SumProp A) (μB : SumProp B)
                  {f} {g} →
                  sum μB f ≡ sum μB g →
                  sum (μA ×μ μB) (f ∘ proj₂) ≡ sum (μA ×μ μB) (g ∘ proj₂)
(μA ×Sum-proj₂' μB) sumf≡sumg = sum-ext μA (const sumf≡sumg)

μ-view : ∀ {A B} → (A FE.⟶ B) → SumPropoid A → SumPropoid B
μ-view {A}{B} A→B μA = searchᴮ , ind
  where
    searchᴮ : Search (Setoid.Carrier B)
    searchᴮ m f = search μA m (f ∘ _⟨$⟩_ A→B)

    ind : SearchInd searchᴮ
    ind P P∙ Pf = search-ind μA (λ s → P (λ _ f → s _ (f ∘ _⟨$⟩_ A→B))) P∙ (Pf ∘ _⟨$⟩_ A→B)

μ-iso : ∀ {A B} → (FI.Inverse A B) → SumPropoid A → SumPropoid B
μ-iso A↔B = μ-view (Inverse.to A↔B)


μ-view-preserve : ∀ {A B} (A→B : A FE.⟶ B)(B→A : B FE.⟶ A)(A≈B : A→B RightInverseOf B→A)
                  (f : A FE.⟶ ≡.setoid ℕ) (μA : SumPropoid A)
                → sum μA (_⟨$⟩_ f) ≡ sum (μ-view A→B μA) (_⟨$⟩_ (f FE.∘  B→A))
μ-view-preserve {A}{B} A→B B→A A≈B f μA = sum-ext μA (λ x → FE.cong f (Setoid.sym A (A≈B x) ))

μ-iso-preserve : ∀ {A B} (A↔B : A ↔ B) f (μA : SumProp A) → sum μA f ≡ sum (μ-iso A↔B μA) (f ∘ _⟨$⟩_ (Inverse.from A↔B))
μ-iso-preserve A↔B f μA = μ-view-preserve (Inverse.to A↔B) (Inverse.from A↔B)
                            (Inverse.left-inverse-of A↔B)
                          (≡.:→-to-Π f) μA

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec.NP as Vec using (Vec; tabulate; _++_) renaming (map to vmap; sum to vsum; foldr to vfoldr; foldr₁ to vfoldr₁)

vmsum : ∀ m {n} → let open Mon m in
                  Vec C n → C
vmsum m = vfoldr _ _∙_ ε
  where open Monoid m

vsgsum : ∀ sg {n} → let open Sgrp sg in
                    Vec C (suc n) → C
vsgsum sg = vfoldr₁ _∙_
  where open Sgrp sg

-- let's recall that: tabulate f ≗ vmap f (allFin n)

-- searchMonFin : ∀ n → SearchMon (Fin n)
-- searchMonFin n m f = vmsum m (tabulate f)

searchFinSuc : ∀ n → Search (Fin (suc n))
searchFinSuc n _∙_ f = vfoldr₁ _∙_ (tabulate f)


μMaybe : ∀ {A} → SumProp A → SumProp (Maybe A)
μMaybe μA = srch , ind where
  srch : Search (Maybe _)
  srch _∙_ f = f nothing ∙ search μA _∙_ (f ∘ just)
  ind : SearchInd srch
  ind P _P∙_ Pf = Pf nothing
               P∙ search-ind μA (λ s → P (λ op f → s op (f ∘ just))  ) _P∙_ (Pf ∘ just)

μMaybeIso : ∀ {A} → SumProp A → SumProp (Maybe A)
μMaybeIso μA = μ-iso (FI.sym Maybe↔𝟙⊎ FI.∘ lift-⊎) (μ𝟙 +μ μA)

μMaybe^ : ∀ {A} n → SumProp A → SumProp (Maybe^ n A)
μMaybe^ zero    μA = μA
μMaybe^ (suc n) μA = μMaybe (μMaybe^ n μA)


μFinSuc : ∀ n → SumProp (Fin (suc n))
μFinSuc n = searchFinSuc n , ind n
  where ind : ∀ n → SearchInd (searchFinSuc n)
        ind zero    P P∙ Pf = Pf zero
        ind (suc n) P P∙ Pf = P∙ (Pf zero) (ind n (λ s → P (λ op f → s op (f ∘ suc))) P∙ (Pf ∘ suc))
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
