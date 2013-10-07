{-# OPTIONS --without-K #-}
-- Constructions on top of exploration functions

open import Level.NP
open import Type hiding (★)
open import Function.NP
open import Algebra.FunctionProperties.NP
open import Data.Two
open import Data.Nat.NP hiding (_^_; _⊔_)
open import Data.Nat.Properties
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Maybe.NP
open import Algebra
open import Data.Product
open import Data.Sum
open import Data.One using (𝟙)
open import Data.Tree.Binary
import Data.List as List
open List using (List; _++_)
open import Relation.Binary
open import Relation.Binary.Sum using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise using (_×-cong_)
import Function.Related as FR
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as FI
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)

open import Explore.Type
import Explore.Monad as EM

module Explore.Explorable where

module FromExplore
    {m A}
    (explore : Explore m A) where

  exploreMon : ∀ {ℓ} (M : Monoid m ℓ) → ExploreMon M A
  exploreMon M = explore _∙_
    where open Mon M

  explore∘ : ∀ {M} → (M → M → M) → (A → M) → (M → M)
  explore∘ = explore∘FromExplore explore

  exploreMon∘ : ∀ {ℓ} (M : Monoid m ℓ) → ExploreMon M A
  exploreMon∘ M f = explore∘ _∙_ f ε where open Mon M

module FromExplore₀ {A} (explore : Explore₀ A) where
  open FromExplore explore

  sum : Sum A
  sum = explore _+_

  Card : ℕ
  Card = sum (const 1)

  count : Count A
  count f = sum (𝟚▹ℕ ∘ f)

  product : (A → ℕ) → ℕ
  product = explore _*_

  big-∧ and big-∨ or big-xor : (A → 𝟚) → 𝟚

  big-∧ = explore _∧_
  and   = big-∧

  big-∨ = explore _∨_
  or    = big-∨

  big-xor = explore _xor_

  toBinTree : BinTree A
  toBinTree = explore fork leaf

  toList : List A
  toList = explore _++_ List.[_]

  toList∘ : List A
  toList∘ = explore∘ _++_ List.[_] List.[]

  find? : Find? A
  find? = explore (M?._∣_ _)

  findKey : FindKey A
  findKey pred = find? (λ x → [0: nothing 1: just x ] (pred x))

module Explorableₘₚ
    {m p A}
    {explore     : Explore m A}
    (explore-ind : ExploreInd p explore) where

  open FromExplore explore public

  explore-sg-ext : ExploreSgExt _ explore
  explore-sg-ext sg {f} {g} f≈°g = explore-ind (λ s → s _ f ≈ s _ g) ∙-cong f≈°g
    where open Sgrp sg

  explore-mono : ExploreMono _ explore
  explore-mono _⊆_ _∙-mono_ {f} {g} f⊆°g =
    explore-ind (λ s → s _ f ⊆ s _ g) _∙-mono_ f⊆°g

  explore-swap : ExploreSwap _ explore
  explore-swap sg f {sᴮ} pf =
    explore-ind (λ s → s _ (sᴮ ∘ f) ≈ sᴮ (s _ ∘ flip f))
               (λ p q → trans (∙-cong p q) (sym (pf _ _)))
               (λ _ → refl)
    where open Sgrp sg

plugKit : ∀ {m p A} (M : Monoid m p) → ExploreIndKit _ {A = A} (ExplorePlug M)
plugKit M = (λ Ps Ps' _ x →
                  trans (∙-cong (sym (Ps _ _)) refl)
                        (trans (assoc _ _ _)
                               (trans (∙-cong refl (Ps' _ x)) (Ps _ _))))
            , (λ x f _ → ∙-cong (proj₂ identity (f x)) refl)
     where open Mon M

module Explorableₘ
    {m A}
    {explore     : Explore m A}
    (explore-ind : ExploreInd m explore) where
  open Explorableₘₚ explore-ind

  explore∘-plug : (M : Monoid m m) → ExplorePlug M explore
  explore∘-plug M = explore-ind $kit plugKit M

  exploreMon∘-spec : ∀ (M : Monoid _ m) →
                      let open Mon M in
                      (f : A → C) → exploreMon M f ≈ exploreMon∘ M f
  exploreMon∘-spec M f = proj₂ (explore-ind
                     (λ s → ExplorePlug M s × s _∙_ f ≈ explore∘FromExplore s _∙_ f ε)
                     (λ {s} {s'} Ps Ps' →
                        P∙ {s} {s'} (proj₁ Ps) (proj₁ Ps')
                      , trans (∙-cong (proj₂ Ps) (proj₂ Ps')) (proj₁ Ps f _))
                     (λ x → Pf x , sym (proj₂ identity _)))
                        where open Mon M
                              open ExploreIndKit (plugKit M)

  explore∘-ind : ∀ (M : Monoid m m) → ExploreMonInd m M (exploreMon∘ M)
  explore∘-ind M P P∙ Pf P≈ =
    proj₂ (explore-ind (λ s → ExplorePlug M s × P (λ f → s _∘′_ (_∙_ ∘ f) ε))
               (λ {s} {s'} Ps Ps' → ExploreIndKit.P∙ (plugKit M) {s} {s'} (proj₁ Ps) (proj₁ Ps')
                                  , P≈ (λ f → proj₁ Ps f _) (P∙ (proj₂ Ps) (proj₂ Ps')))
               (λ x → ExploreIndKit.Pf (plugKit M) x
                    , P≈ (λ f → sym (proj₂ identity _)) (Pf x)))
    where open Mon M

  explore-ext : ExploreExt explore
  explore-ext op = explore-ind (λ s → s _ _ ≡ s _ _) (≡.cong₂ op)

  ⟦explore⟧ᵤ : ∀ {Aᵣ : A → A → ★_ _}
               (Aᵣ-refl : Reflexive Aᵣ)
              → ⟦Explore⟧ᵤ Aᵣ explore explore
  ⟦explore⟧ᵤ Aᵣ-refl Mᵣ ∙ᵣ fᵣ = explore-ind (λ s → Mᵣ (s _ _) (s _ _)) (λ η → ∙ᵣ η) (λ η → fᵣ Aᵣ-refl)

  explore-ε : Exploreε m m explore
  explore-ε M = explore-ind (λ s → s _ (const ε) ≈ ε)
                          (λ x≈ε y≈ε → trans (∙-cong x≈ε y≈ε) (proj₁ identity ε))
                          (λ _ → refl)
    where open Mon M

  explore-hom : ExploreMonHom m m explore
  explore-hom cm f g = explore-ind (λ s → s _ (f ∙° g) ≈ s _ f ∙ s _ g)
                                 (λ p₀ p₁ → trans (∙-cong p₀ p₁) (∙-interchange _ _ _ _)) (λ _ → refl)
    where open CMon cm

  explore-linˡ : ExploreLinˡ m m explore
  explore-linˡ m _◎_ f k dist = explore-ind (λ s → s _∙_ (λ x → k ◎ f x) ≈ k ◎ s _∙_ f) (λ x x₁ → trans (∙-cong x x₁) (sym (dist k _ _))) (λ x → refl)
    where open Mon m

  explore-linʳ : ExploreLinʳ m m explore
  explore-linʳ m _◎_ f k dist = explore-ind (λ s → s _∙_ (λ x → f x ◎ k) ≈ s _∙_ f ◎ k) (λ x x₁ → trans (∙-cong x x₁) (sym (dist k _ _))) (λ x → refl)
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

        lift-hom : f (explore _+_ g) ≈ explore _*_ (f ∘ g)
        lift-hom = explore-ind (λ s → f (s _+_ g) ≈ s _*_ (f ∘ g))
                               (λ p q → ≈-trans (hom _ _) (≈-cong-* p q))
                               (λ _ → ≈-refl)

  lift-hom-≡ :
      ∀ {S T}
        (_+_ : Op₂ S)
        (_*_ : Op₂ T)
        (f   : S → T)
        (g   : A → S)
        (hom : ∀ x y → f (x + y) ≡ f x * f y)
      → f (explore _+_ g) ≡ explore _*_ (f ∘ g)
  lift-hom-≡ _+_ _*_ = lift-hom _≡_ ≡.refl ≡.trans _+_ _*_ (≡.cong₂ _*_)

module Explorable₀
    {A}
    {explore     : Explore₀ A}
    (explore-ind : ExploreInd₀ explore) where
  open Explorableₘₚ explore-ind public
  open Explorableₘ  explore-ind public
  open FromExplore₀ explore     public

  ⟦explore⟧ : ∀ {Aᵣ : A → A → ★_ _}
               (Aᵣ-refl : Reflexive Aᵣ)
              → ⟦Explore⟧ Aᵣ explore explore
  ⟦explore⟧ = ⟦explore⟧ᵤ

  sum-ind : SumInd sum
  sum-ind P P+ Pf = explore-ind (λ s → P (s _+_)) P+ Pf

  sum-ext : SumExt sum
  sum-ext = explore-ext _+_

  sum-zero : SumZero sum
  sum-zero = explore-ε ℕ+.monoid

  sum-hom : SumHom sum
  sum-hom = explore-hom ℕ°.+-commutativeMonoid

  sum-mono : SumMono sum
  sum-mono = explore-mono _≤_ _+-mono_

  sum-swap' : ∀ {B}{sumμB : Sum B}(μB : SumHom sumμB) f →
             sum (sumμB ∘ f) ≡ sumμB (sum ∘ flip f)
  sum-swap' {B}{sumB} μB f = explore-ind (λ E → E _+_ (sumB ∘ f) ≡ sumB (E _+_ ∘ flip f))
     (λ p q → ≡.trans (≡.cong₂ _+_ p q) (≡.sym (μB _ _))) (λ _ → ≡.refl)
  
  sum-lin : SumLin sum
  sum-lin f zero    = sum-zero
  sum-lin f (suc k) = ≡.trans (sum-hom f (λ x → k * f x)) (≡.cong₂ _+_ (≡.refl {x = sum f}) (sum-lin f k))
  
  sum-const : SumConst sum
  sum-const x = ≡.trans (≡.trans (sum-ext (λ _ → ≡.sym (proj₂ ℕ°.*-identity x))) (sum-lin (const 1) x)) (ℕ°.*-comm x Card)
  
  sumStableUnder : ∀ {p} → StableUnder explore p → SumStableUnder sum p
  sumStableUnder SU-p = SU-p _+_

  count-ext : CountExt count
  count-ext f≗g = sum-ext (≡.cong 𝟚▹ℕ ∘ f≗g)

  countStableUnder : ∀ {p} → SumStableUnder sum p → CountStableUnder count p
  countStableUnder sumSU-p f = sumSU-p (𝟚▹ℕ ∘ f)

  toList≡toList∘ : toList ≡ toList∘
  toList≡toList∘ = exploreMon∘-spec (List.monoid A) List.[_]

module AdequateSum₀
  {A}{B}
  {sumᴬ : Sum A}{sumᴮ : Sum B}
  (sumᴬ-adq : AdequateSum sumᴬ)
  (sumᴮ-adq : AdequateSum sumᴮ) where

  sumStableUnder : (p : A ↔ B)(f : A → ℕ)
                 → sumᴬ f ≡ sumᴮ (f ∘ from p)
  sumStableUnder p f = Fin-injective (FI.sym (sumᴮ-adq (f ∘ from p))
                                  FI.∘ first-iso p
                                  FI.∘ sumᴬ-adq f)
module EndoAdequateSum₀
  {A}
  {sum : Sum A}
  (sum-adq : AdequateSum sum) where

  open AdequateSum₀ sum-adq sum-adq public

  module _ (p q : A → 𝟚)(prf : sum (𝟚▹ℕ ∘ p) ≡ sum (𝟚▹ℕ ∘ q)) where
    private

        P = λ x → p x ≡ 1₂
        Q = λ x → q x ≡ 1₂
        ¬P = λ x → p x ≡ 0₂
        ¬Q = λ x → q x ≡ 0₂
    
        Fin-reflexive : ∀ {n m} → n ≡ m → Fin n ↔ Fin m
        Fin-reflexive eq rewrite eq = FI.id
    
        Fin↔≡1₂ : ∀ b → Fin (𝟚▹ℕ b) ↔ b ≡ 1₂
        Fin↔≡1₂ 1₂ = inverses (λ x → ≡.refl) (λ _ → _) (λ x → ≡.refl) (λ x → ≡.proof-irrelevance ≡.refl x) FI.∘ Fin1↔𝟙
        Fin↔≡1₂ 0₂ = inverses (λ ()) (λ ()) (λ ()) (λ ())

        Fin↔≡0₂ : ∀ b → Fin (𝟚▹ℕ (not b)) ↔ b ≡ 0₂
        Fin↔≡0₂ b = FI.sym (≡-iso (not-𝟚↔𝟚)) FI.∘ Fin↔≡1₂ (not b)
        
        count-≡ : ∀ (p : A → 𝟚) x → Fin (𝟚▹ℕ (p x)) ↔ p x ≡ 1₂
        count-≡ p x = Fin↔≡1₂ (p x)
        
        lem1 : ∀ px qx → 𝟚▹ℕ qx ≡ (𝟚▹ℕ (px ∧ qx)) + 𝟚▹ℕ (not px) * 𝟚▹ℕ qx
        lem1 1₂ 1₂ = ≡.refl
        lem1 1₂ 0₂ = ≡.refl
        lem1 0₂ 1₂ = ≡.refl
        lem1 0₂ 0₂ = ≡.refl

        lem2 : ∀ px qx → 𝟚▹ℕ px ≡ (𝟚▹ℕ (px ∧ qx)) + 𝟚▹ℕ px * 𝟚▹ℕ (not qx)
        lem2 1₂ 1₂ = ≡.refl
        lem2 1₂ 0₂ = ≡.refl
        lem2 0₂ 1₂ = ≡.refl
        lem2 0₂ 0₂ = ≡.refl
        
        lemma1 : ∀ px qx → qx ≡ 1₂ ↔ (Fin (𝟚▹ℕ (px ∧ qx)) ⊎ (px ≡ 0₂ × qx ≡ 1₂))
        lemma1 px qx = FI.id ⊎-cong (Fin↔≡0₂ px ×-cong Fin↔≡1₂ qx)
                  FI.∘ FI.id ⊎-cong FI.sym (Fin-×-* (𝟚▹ℕ (not px)) (𝟚▹ℕ qx))
                  FI.∘ FI.sym (Fin-⊎-+ (𝟚▹ℕ (px ∧ qx)) (𝟚▹ℕ (not px) * 𝟚▹ℕ qx))
                  FI.∘ Fin-reflexive (lem1 px qx)
                  FI.∘ FI.sym (Fin↔≡1₂ qx)
        
        lemma2 : ∀ px qx → (Fin (𝟚▹ℕ (px ∧ qx)) ⊎ (px ≡ 1₂ × qx ≡ 0₂)) ↔ px ≡ 1₂
        lemma2 px qx = Fin↔≡1₂ px
                  FI.∘ Fin-reflexive (≡.sym (lem2 px qx))
                  FI.∘ Fin-⊎-+ _ _ 
                  FI.∘ FI.id ⊎-cong (Fin-×-* _ _)
                  FI.∘ FI.sym (FI.id ⊎-cong (Fin↔≡1₂ px ×-cong Fin↔≡0₂ qx))

        iso : Σ A P ↔ Σ A Q
        iso = second-iso (count-≡ q)
               FI.∘ sum-adq (𝟚▹ℕ ∘ q)
               FI.∘ Fin-reflexive prf
               FI.∘ FI.sym (sum-adq (𝟚▹ℕ ∘ p))
               FI.∘ FI.sym (second-iso (count-≡ p))
  
        iso' : (Fin (sum (λ x → 𝟚▹ℕ (p x ∧ q x))) ⊎ Σ A (λ x →  P x × ¬Q x))
             ↔ (Fin (sum (λ x → 𝟚▹ℕ (p x ∧ q x))) ⊎ Σ A (λ x → ¬P x ×  Q x))
        iso' = FI.sym (sum-adq (λ x → 𝟚▹ℕ (p x ∧ q x))) ⊎-cong FI.id
          FI.∘ Σ-⊎-hom
          FI.∘ second-iso (λ x → lemma1 (p x) (q x))
          FI.∘ iso
          FI.∘ second-iso (λ x → lemma2 (p x ) (q x))
          FI.∘ FI.sym Σ-⊎-hom
          FI.∘ (sum-adq (λ x → 𝟚▹ℕ (p x ∧ q x))) ⊎-cong FI.id
               
        iso'' : Σ A (λ x →  P x × ¬Q x)
              ↔ Σ A (λ x → ¬P x ×  Q x)
        iso'' = Fin⊎-injective (sum (λ x → 𝟚▹ℕ (p x ∧ q x))) iso'
  
        module M = Work-In-Progress (to iso'') (from iso'') (Inverse.left-inverse-of iso'')
                                    (Inverse.right-inverse-of iso'')
    
    indIso : A ↔ A
    indIso = inverses M.π M.π M.ππ M.ππ
      
    indIsIso : ∀ x → p x ≡ q (from indIso x)
    indIsIso x = M.prop x
  
module Explorable₁₀ {A} {explore₁ : Explore₁ A}
                    (explore-ind₀ : ExploreInd ₀ explore₁) where

  reify : Reify explore₁
  reify = explore-ind₀ (λ s → DataΠ s _) _,_

module Explorable₁₁ {A} {explore₁ : Explore₁ A}
                    (explore-ind₁ : ExploreInd ₁ explore₁) where

  unfocus : Unfocus explore₁
  unfocus = explore-ind₁ Unfocus (λ P Q → [ P , Q ]) (λ η → _,_ η)

record Explorable A : ★₁ where
  constructor mk
  field
    explore     : Explore₀ A
    explore-ind : ExploreInd₀ explore

  open Explorable₀ explore-ind
  field
    adequate-sum     : AdequateSum sum
--  adequate-product : AdequateProduct product

  open Explorable₀ explore-ind public

open Explorable public

ExploreForFun : ★₀ → ★₁
ExploreForFun A = ∀ {X} → Explorable X → Explorable (A → X)

record Funable A : ★₂ where
  constructor _,_
  field
    explorable : Explorable A
    negative   : ExploreForFun A

module DistFun {A} (μA : Explorable A)
                   (μA→ : ExploreForFun A)
                   {B} (μB : Explorable B){X}
                   (_≈_ : X → X → ★ ₀)
                   (∙ : X → X → X)
                   (◎ : X → X → X) where

  Π' = explore μA ◎
  Σᴮ = explore μB ∙
  Σ' = explore (μA→ μB) ∙

  DistFun = ∀ f → Π' (Σᴮ ∘ f) ≈ Σ' (Π' ∘ _ˢ_ f)

DistFun : ∀ {A} → Explorable A → ExploreForFun A → ★₁
DistFun μA μA→ = ∀ {B} (μB : Explorable B) c → let open CMon {₀}{₀} c in
                   ∀ ◎ → _DistributesOver_ _≈_ ◎ _∙_ → ◎ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
                   → DistFun.DistFun μA μA→ μB _≈_ _∙_ ◎

DistFunable : ∀ {A} → Funable A → ★₁
DistFunable (μA , μA→) = DistFun μA μA→

μ-iso : ∀ {A B} → (A ↔ B) → Explorable A → Explorable B
μ-iso {A}{B} A↔B μA = mk (EM.map _ A→B (explore μA)) (EM.map-ind _ A→B (explore-ind μA)) ade
  where
    A→B = to A↔B
    ade = λ f → sym-first-iso A↔B FI.∘ adequate-sum μA (f ∘ A→B)

-- I guess this could be more general
μ-iso-preserve : ∀ {A B} (A↔B : A ↔ B) f (μA : Explorable A) → sum μA f ≡ sum (μ-iso A↔B μA) (f ∘ from A↔B)
μ-iso-preserve A↔B f μA = sum-ext μA (≡.cong f ∘ ≡.sym ∘ Inverse.left-inverse-of A↔B)

μLift : ∀ {A} → Explorable A → Explorable (Lift A)
μLift = μ-iso (FI.sym Lift↔id)

explore-swap' : ∀ {A B} cm (μA : Explorable A) (μB : Explorable B) f →
               let open CMon cm
                   sᴬ = explore μA _∙_
                   sᴮ = explore μB _∙_ in
               sᴬ (sᴮ ∘ f) ≈ sᴮ (sᴬ ∘ flip f)
explore-swap' cm μA μB f = explore-swap μA sg f (explore-hom μB cm)
  where open CMon cm

sum-swap : ∀ {A B} (μA : Explorable A) (μB : Explorable B) f →
           sum μA (sum μB ∘ f) ≡ sum μB (sum μA ∘ flip f)
sum-swap = explore-swap' ℕ°.+-commutativeMonoid
