import Level as L
open L using (Lift) renaming (zero to ₀)
open import Type hiding (★)
open import Function.NP
open import Search.Type
open import Algebra.FunctionProperties.NP
open import Data.Bool.NP as Bool
open import Data.Nat.NP hiding (_^_; _⊔_)
open import Data.Nat.Properties
open import Data.Fin using (Fin)
open import Data.Maybe.NP
open import Algebra
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤)
open import Data.Tree.Binary
import Data.List as List
open List using (List; _++_)
open import Relation.Binary
import Function.Related as FR
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as FI
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)

module Search.Searchable where

private
  ₁ = L.suc ₀

fromBinTree : ∀ {m A} → BinTree A → Search m A
fromBinTree (leaf x)   _   f = f x
fromBinTree (fork ℓ r) _∙_ f = fromBinTree ℓ _∙_ f ∙ fromBinTree r _∙_ f

fromBinTree-ind : ∀ {m p A} (t : BinTree A) → SearchInd p (fromBinTree {m} t)
fromBinTree-ind (leaf x)   P P∙ Pf = Pf x
fromBinTree-ind (fork ℓ r) P P∙ Pf = P∙ (fromBinTree-ind ℓ P P∙ Pf)
                                        (fromBinTree-ind r P P∙ Pf)

plugKit : ∀ {m p A} (M : Monoid m p) → SearchIndKit _ {A = A} (SearchPlug M)
plugKit M = (λ Ps Ps' _ x →
                  trans (∙-cong (sym (Ps _ _)) refl)
                        (trans (assoc _ _ _)
                               (trans (∙-cong refl (Ps' _ x)) (Ps _ _))))
            , (λ x f _ → ∙-cong (proj₂ identity (f x)) refl)
     where open Mon M

module Searchableₘₚ
    {m p A}
    {search     : Search m A}
    (search-ind : SearchInd p search) where

  search-sg-ext : SearchSgExt _ search
  search-sg-ext sg {f} {g} f≈°g = search-ind (λ s → s _ f ≈ s _ g) ∙-cong f≈°g
    where open Sgrp sg

  search-mono : SearchMono _ search
  search-mono _⊆_ _∙-mono_ {f} {g} f⊆°g =
    search-ind (λ s → s _ f ⊆ s _ g) _∙-mono_ f⊆°g

  search-swap : SearchSwap _ search
  search-swap sg f {sᴮ} pf =
    search-ind (λ s → s _ (sᴮ ∘ f) ≈ sᴮ (s _ ∘ flip f))
               (λ p q → trans (∙-cong p q) (sym (pf _ _)))
               (λ _ → refl)
    where open Sgrp sg

  searchMon : ∀ {ℓ} (M : Monoid m ℓ) → SearchMon M A
  searchMon M = search _∙_
    where open Mon M

  search∘ : ∀ {M} → (M → M → M) → (A → M) → (M → M)
  search∘ = search∘FromSearch search

  searchMon∘ : ∀ {ℓ} (M : Monoid m ℓ) → SearchMon M A
  searchMon∘ M f = search∘ _∙_ f ε where open Mon M

module Searchableₘ
    {m A}
    {search     : Search m A}
    (search-ind : SearchInd m search) where
  open Searchableₘₚ search-ind

  search∘-plug : (M : Monoid m m) → SearchPlug M search
  search∘-plug M = search-ind $kit plugKit M

  searchMon∘-spec : ∀ (M : Monoid _ m) →
                      let open Mon M in
                      (f : A → C) → searchMon M f ≈ searchMon∘ M f
  searchMon∘-spec M f = proj₂ (search-ind
                     (λ s → SearchPlug M s × s _∙_ f ≈ search∘FromSearch s _∙_ f ε)
                     (λ {s} {s'} Ps Ps' →
                        P∙ {s} {s'} (proj₁ Ps) (proj₁ Ps')
                      , trans (∙-cong (proj₂ Ps) (proj₂ Ps')) (proj₁ Ps f _))
                     (λ x → Pf x , sym (proj₂ identity _)))
                        where open Mon M
                              open SearchIndKit (plugKit M)

  search∘-ind : ∀ (M : Monoid m m) → SearchMonInd m M (searchMon∘ M)
  search∘-ind M P P∙ Pf P≈ =
    proj₂ (search-ind (λ s → SearchPlug M s × P (λ f → s _∘′_ (_∙_ ∘ f) ε))
               (λ {s} {s'} Ps Ps' → SearchIndKit.P∙ (plugKit M) {s} {s'} (proj₁ Ps) (proj₁ Ps')
                                  , P≈ (λ f → proj₁ Ps f _) (P∙ (proj₂ Ps) (proj₂ Ps')))
               (λ x → SearchIndKit.Pf (plugKit M) x
                    , P≈ (λ f → sym (proj₂ identity _)) (Pf x)))
    where open Mon M

  search-ext : SearchExt search
  search-ext op = search-ind (λ s → s _ _ ≡ s _ _) (≡.cong₂ op)

  ⟦search⟧ᵤ : ∀ {Aᵣ : A → A → ★_ _}
               (Aᵣ-refl : Reflexive Aᵣ)
              → ⟦Search⟧ᵤ Aᵣ search search
  ⟦search⟧ᵤ Aᵣ-refl Mᵣ ∙ᵣ fᵣ = search-ind (λ s → Mᵣ (s _ _) (s _ _)) (λ η → ∙ᵣ η) (λ η → fᵣ Aᵣ-refl)

  search-ε : Searchε m m search
  search-ε M = search-ind (λ s → s _ (const ε) ≈ ε)
                          (λ x≈ε y≈ε → trans (∙-cong x≈ε y≈ε) (proj₁ identity ε))
                          (λ _ → refl)
    where open Mon M

  search-hom : SearchMonHom m m search
  search-hom cm f g = search-ind (λ s → s _ (f ∙° g) ≈ s _ f ∙ s _ g)
                                 (λ p₀ p₁ → trans (∙-cong p₀ p₁) (∙-interchange _ _ _ _)) (λ _ → refl)
    where open CMon cm

  search-linˡ : SearchLinˡ m m search
  search-linˡ m _◎_ f k dist = search-ind (λ s → s _∙_ (λ x → k ◎ f x) ≈ k ◎ s _∙_ f) (λ x x₁ → trans (∙-cong x x₁) (sym (dist k _ _))) (λ x → refl)
    where open Mon m

  search-linʳ : SearchLinʳ m m search
  search-linʳ m _◎_ f k dist = search-ind (λ s → s _∙_ (λ x → f x ◎ k) ≈ s _∙_ f ◎ k) (λ x x₁ → trans (∙-cong x x₁) (sym (dist k _ _))) (λ x → refl)
    where open Mon m

  module _
       {S T : ★ m}
        (_≈_ : T → T → ★ m)
        (≈-refl : Reflexive _≈_)
        (≈-trans : Transitive _≈_)
        (_+_ : Op₂ S)
        (_*_ : Op₂ T)
        (≈-cong-* : _*_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_)
        (f   : S → T)
        (g   : A → S)
        (hom : ∀ x y → (f (x + y)) ≈ (f x * f y))
        where

        search-hom′′ : f (search _+_ g) ≈ search _*_ (f ∘ g)
        search-hom′′ = search-ind (λ s → f (s _+_ g) ≈ s _*_ (f ∘ g))
                                                  (λ p q → ≈-trans (hom _ _) (≈-cong-* p q))
                                                  (λ _ → ≈-refl)

  search-hom′ :
      ∀ {S T}
        (_+_ : Op₂ S)
        (_*_ : Op₂ T)
        (f   : S → T)
        (g   : A → S)
        (hom : ∀ x y → f (x + y) ≡ f x * f y)
        → f (search _+_ g) ≡ search _*_ (f ∘ g)
  search-hom′ _+_ _*_ = search-hom′′ _≡_ ≡.refl ≡.trans _+_ _*_ (≡.cong₂ _*_)

module Searchable₀
    {A}
    {search     : Search₀ A}
    (search-ind : SearchInd₀ search) where
  open Searchableₘₚ search-ind public
  open Searchableₘ  search-ind public

  sum : Sum A
  sum = search _+_

  ⟦search⟧ : ∀ {Aᵣ : A → A → ★_ _}
               (Aᵣ-refl : Reflexive Aᵣ)
              → ⟦Search⟧ Aᵣ search search
  ⟦search⟧ = ⟦search⟧ᵤ

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

  sumStableUnder : ∀ {p} → StableUnder search p → SumStableUnder sum p
  sumStableUnder SU-p = SU-p _+_

  Card : ℕ
  Card = sum (const 1)

  count : Count A
  count f = sum (Bool.toℕ ∘ f)

  count-ext : CountExt count
  count-ext f≗g = sum-ext (≡.cong Bool.toℕ ∘ f≗g)

  countStableUnder : ∀ {p} → SumStableUnder sum p → CountStableUnder count p
  countStableUnder sumSU-p f = sumSU-p (Bool.toℕ ∘ f)

  product : (A → ℕ) → ℕ
  product = search _*_

  toBinTree : BinTree A
  toBinTree = search fork leaf

  toList : List A
  toList = search _++_ List.[_]

  toList∘ : List A
  toList∘ = search∘ _++_ List.[_] List.[]

  toList≡toList∘ : toList ≡ toList∘
  toList≡toList∘ = searchMon∘-spec (List.monoid A) List.[_]

  find? : Find? A
  find? = search (M?._∣_ _)

  findKey : FindKey A
  findKey pred = find? (λ x → if pred x then just x else nothing)

  {-
module BigDistr {A B : ★₀}
                {searchᴬ : Search₀ A} 
                {searchᴮ : Search₀ B} 
                {searchᴬᴮ : Search₀ (A → B)}
                (F : A → B → ℕ)
                where
  productᴬ = searchᴬ _*_
  sumᴮ = searchᴮ _+_
  sumᴬᴮ = searchᴬᴮ _+_

  module _
    (adequate-productᴬ : AdequateProduct productᴬ)
    (adequate-sumᴮ : AdequateSum sumᴮ)
    (adequate-sumᴬᴮ : AdequateSum sumᴬᴮ)
    where

    open FR.EquationalReasoning
    big-distr :
      productᴬ (sumᴮ ∘ F) ≡
      sumᴬᴮ (λ f → productᴬ (F ˢ f))
    big-distr = Fin-injective (
        Fin (productᴬ (sumᴮ ∘ F))
      ↔⟨ adequate-productᴬ (sumᴮ ∘ F) ⟩
        Π A (Fin ∘ sumᴮ ∘ F)
      ↔⟨ {!adequate-sumᴮ!} ⟩
        Π A (λ x → Σ B (Fin ∘ F x))
      ↔⟨ dep-choice-iso _ ⟩
        Σ (Π A (const B)) (λ f → Π A (λ x → Fin (F x (f x))))
      ↔⟨ second-iso (λ f → sym (adequate-productᴬ (F ˢ f))) ⟩
        Σ (Π A (const B)) (λ f → Fin (productᴬ (F ˢ f)))
      ↔⟨ sym (adequate-sumᴬᴮ (λ f → productᴬ (F ˢ f))) ⟩
        Fin (sumᴬᴮ (λ f → productᴬ (F ˢ f)))
      ∎)
-}

module Searchable₁₀ {A} {search₁ : Search₁ A}
                    (search-ind₀ : SearchInd ₀ search₁) where

  reify : Reify search₁
  reify = search-ind₀ (λ s → DataΠ s _) _,_

module Searchable₁₁ {A} {search₁ : Search₁ A}
                    (search-ind₁ : SearchInd ₁ search₁) where

  unfocus : Unfocus search₁
  unfocus = search-ind₁ Unfocus (λ P Q → [ P , Q ]) (λ η → _,_ η)

record Searchable A : ★₁ where
  constructor mk
  field
    search     : Search₀ A
    search-ind : SearchInd₀ search

  open Searchable₀ search-ind
  field
    adequate-sum     : AdequateSum sum
-- TODO (maybe)
--    adequate-product : AdequateProduct product

  open Searchable₀ search-ind public

open Searchable public

SearchForFun : ★₀ → ★₁
SearchForFun A = ∀ {X} → Searchable X → Searchable (A → X)

record Funable A : ★₂ where
  constructor _,_
  field
    searchable : Searchable A
    negative   : SearchForFun A

module DistFun {A} (μA : Searchable A)
                   (μA→ : SearchForFun A)
                   {B} (μB : Searchable B){X}
                   (_≈_ : X → X → ★ ₀)
                   (∙ : X → X → X)
                   (◎ : X → X → X) where

  Π' = search μA ◎
  Σᴮ = search μB ∙
  Σ' = search (μA→ μB) ∙

  DistFun = ∀ f → Π' (Σᴮ ∘ f) ≈ Σ' (Π' ∘ _ˢ_ f)


DistFun : ∀ {A} → Searchable A → SearchForFun A → ★₁
DistFun μA μA→ = ∀ {B} (μB : Searchable B) c → let open CMon {L.zero}{L.zero} c in
                   ∀ ◎ → _DistributesOver_ _≈_ ◎ _∙_ → ◎ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
                   → DistFun.DistFun μA μA→ μB _≈_ _∙_ ◎


DistFunable : ∀ {A} → Funable A → ★₁
DistFunable (μA , μA→) = DistFun μA μA→

μ-iso : ∀ {A B} → (A ↔ B) → Searchable A → Searchable B
μ-iso {A}{B} A↔B μA = mk searchᴮ ind ade
  where
    A→B = to A↔B

    searchᴮ : Search _ B
    searchᴮ m f = search μA m (f ∘ A→B)

    sumᴮ = searchᴮ _+_

    ind : SearchInd _ searchᴮ
    ind P P∙ Pf = search-ind μA (λ s → P (λ _ f → s _ (f ∘ A→B))) P∙ (Pf ∘ A→B)

    ade : AdequateSum sumᴮ
    ade f = sym-first-iso A↔B FI.∘ adequate-sum μA (f ∘ A→B)

-- I guess this could be more general
μ-iso-preserve : ∀ {A B} (A↔B : A ↔ B) f (μA : Searchable A) → sum μA f ≡ sum (μ-iso A↔B μA) (f ∘ from A↔B)
μ-iso-preserve A↔B f μA = sum-ext μA (≡.cong f ∘ ≡.sym ∘ Inverse.left-inverse-of A↔B)

μLift : ∀ {A} → Searchable A → Searchable (Lift A)
μLift = μ-iso (FI.sym Lift↔id)

μ⊤ : Searchable ⊤
μ⊤ = mk _ ind ade
  where
    srch : Search _ ⊤
    srch _ f = f _

    ind : SearchInd _ srch
    ind _ _ Pf = Pf _

    ade : AdequateSum (srch _+_)
    ade x = FI.sym ⊤×A↔A
