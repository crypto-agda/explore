{-# OPTIONS --without-K #-}
-- Constructions on top of exploration functions

open import Level.NP
open import Type hiding (★)
open import Type.Identities
open import Function.NP
open import Function.Extensionality
open import Algebra.FunctionProperties.NP
open import Data.Two
open import Data.Indexed
open import Data.Nat.NP hiding (_^_; _⊔_)
open import Data.Nat.Properties
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Maybe.NP
open import Algebra
open import Data.Product renaming (map to ×-map)
open import Data.Sum
open import Data.Zero using (𝟘)
open import Data.One using (𝟙)
open import Data.Tree.Binary
import Data.List as List
open List using (List; _++_)
open import Relation.Nullary.NP
open import Relation.Binary
open import Relation.Binary.Sum using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise using (_×-cong_)
import Function.Related as FR
import Relation.Binary.PropositionalEquality.NP as ≡
open import HoTT
open Equivalences
open ≡ using (_≡_)

open import Explore.Core
open import Explore.Properties
import Explore.Monad as EM

module Explore.Explorable where

module _ {m} {A : ★₀} where
  open EM m
  gfilter-explore : ∀ {B} → (A →? B) → Explore m A → Explore m B
  gfilter-explore f eᴬ = eᴬ >>= λ x → maybe (λ η → point-explore η) empty-explore (f x)

  filter-explore : (A → 𝟚) → Explore m A → Explore m A
  filter-explore p = gfilter-explore λ x → [0: nothing 1: just x ] (p x)

  -- monoidal exploration: explore A with a monoid M
  explore-monoid : ∀ {ℓ} → Explore m A → ExploreMon m ℓ A
  explore-monoid eᴬ M = eᴬ ε _·_ where open Mon M renaming (_∙_ to _·_)

  explore-endo : Explore m A → Explore m A
  explore-endo eᴬ ε op f = eᴬ id _∘′_ (op ∘ f) ε

  explore-endo-monoid : ∀ {ℓ} → Explore m A → ExploreMon m ℓ A
  explore-endo-monoid = explore-monoid ∘ explore-endo

  explore-backward : Explore m A → Explore m A
  explore-backward eᴬ ε _∙_ f = eᴬ ε (flip _∙_) f

  -- explore-backward ∘ explore-backward = id
  -- (m : a comm monoid) → explore-backward m = explore m

module FromExplore
    {m A}
    (explore : Explore m A) where

  with-monoid : ∀ {ℓ} → ExploreMon m ℓ A
  with-monoid = explore-monoid explore

  with∘ : Explore m A
  with∘ = explore-endo explore

  with-endo-monoid : ∀ {ℓ} → ExploreMon m ℓ A
  with-endo-monoid = explore-endo-monoid explore

  backward : Explore m A
  backward = explore-backward explore

  gfilter : ∀ {B} → (A →? B) → Explore _ B
  gfilter f = gfilter-explore f explore

  filter : (A → 𝟚) → Explore _ A
  filter p = filter-explore p explore

private
  module FindForward {A} (explore : Explore₀ A) where
    find? : Find? A
    find? = explore nothing (M?._∣_ _)

    first : Maybe A
    first = find? just

    findKey : FindKey A
    findKey pred = find? (λ x → [0: nothing 1: just x ] (pred x))

module FromExplore₀ {A} (explore : Explore₀ A) where
  open FromExplore explore

  sum : Sum A
  sum = explore 0 _+_

  Card : ℕ
  Card = sum (const 1)

  count : Count A
  count f = sum (𝟚▹ℕ ∘ f)

  product : (A → ℕ) → ℕ
  product = explore 1 _*_

  big-∧ and big-∨ or big-xor : (A → 𝟚) → 𝟚

  big-∧ = explore 1₂ _∧_
  and   = big-∧
  all   = big-∧

  big-∨ = explore 0₂ _∨_
  or    = big-∨
  any   = big-∨

  big-xor = explore 0₂ _xor_

  bin-tree : BinTree A
  bin-tree = explore empty fork leaf

  list : List A
  list = explore List.[] _++_ List.[_]

  module FindBackward = FindForward backward

  findLast? : Find? A
  findLast? = FindBackward.find?

  last : Maybe A
  last = FindBackward.first

  findLastKey : FindKey A
  findLastKey = FindBackward.findKey

  open FindForward explore public

module Explorableₘₚ
    {m p A}
    {explore     : Explore m A}
    (explore-ind : ExploreInd p explore) where

  open FromExplore explore public

  explore-mon-ext : ExploreMonExt _ explore
  explore-mon-ext m {f} {g} f≈°g = explore-ind (λ s → s _ _ f ≈ s _ _ g) refl ∙-cong f≈°g
    where open Mon m

  explore-mono : ExploreMono _ explore
  explore-mono _⊆_ z⊆ _∙-mono_ {f} {g} f⊆°g =
    explore-ind (λ e → e _ _ f ⊆ e _ _ g) z⊆ _∙-mono_ f⊆°g

  explore-swap : ExploreSwap _ explore
  explore-swap mon {eᴮ} eᴮ-ε pf f =
    explore-ind (λ e → e _ _ (eᴮ ∘ f) ≈ eᴮ (e _ _ ∘ flip f))
                (sym eᴮ-ε)
                (λ p q → trans (∙-cong p q) (sym (pf _ _)))
                (λ _ → refl)
    where open Mon mon

  module LiftHom
       {S T : ★ m}
       (_≈_ : T → T → ★ p)
       (≈-refl : Reflexive _≈_)
       (≈-trans : Transitive _≈_)
       (zero : S)
       (_+_  : Op₂ S)
       (one  : T)
       (_*_  : Op₂ T)
       (≈-cong-* : _*_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_)
       (f   : S → T)
       (g   : A → S)
       (hom-0-1 : f zero ≈ one)
       (hom-+-* : ∀ x y → (f (x + y)) ≈ (f x * f y))
       where

        lift-hom : f (explore zero _+_ g) ≈ explore one _*_ (f ∘ g)
        lift-hom = explore-ind (λ e → f (e zero _+_ g) ≈ e one _*_ (f ∘ g))
                               hom-0-1
                               (λ p q → ≈-trans (hom-+-* _ _) (≈-cong-* p q))
                               (λ _ → ≈-refl)

module ExplorePlug where
    record ExploreIndKit p {ℓ A} (P : Explore ℓ A → ★ p) : ★ (ₛ ℓ ⊔ p) where
      constructor mk
      field
        Pε : P empty-explore
        P∙ : ∀ {e₀ e₁ : Explore ℓ A} → P e₀ → P e₁ → P (merge-explore e₀ e₁)
        Pf : ∀ x → P (point-explore x)

    _$kit_ : ∀ {p ℓ A} {P : Explore ℓ A → ★ p} {e : Explore ℓ A}
             → ExploreInd p e → ExploreIndKit p P → P e
    _$kit_ {P = P} ind (mk Pε P∙ Pf) = ind P Pε P∙ Pf

    _,-kit_ : ∀ {m p A} {P : Explore m A → ★ p}{Q : Explore m A → ★ p}
              → ExploreIndKit p P → ExploreIndKit p Q → ExploreIndKit p (P ×° Q)
    Pk ,-kit Qk = mk (Pε Pk , Pε Qk)
                     (λ x y → P∙ Pk (proj₁ x) (proj₁ y) , P∙ Qk (proj₂ x) (proj₂ y))
                     (λ x → Pf Pk x , Pf Qk x)
                 where open ExploreIndKit

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

    ExplorePlug : ∀ {m ℓ A} (M : Monoid m ℓ) (e : Explore _ A) → ★ _
    ExplorePlug M e = ∀ f x → e∘ ε _∙_ f ∙ x ≈ e∘ x _∙_ f
       where open Mon M
             e∘ = explore-endo e

    plugKit : ∀ {m p A} (M : Monoid m p) → ExploreIndKit _ {A = A} (ExplorePlug M)
    plugKit M = mk (λ _ → proj₁ identity)
                   (λ Ps Ps' _ x →
                      trans (∙-cong (sym (Ps _ _)) refl)
                            (trans (assoc _ _ _)
                                   (trans (∙-cong refl (Ps' _ x)) (Ps _ _))))
                   (λ x f _ → ∙-cong (proj₂ identity (f x)) refl)
         where open Mon M

module Explorableₘ
    {m A}
    {explore     : Explore m A}
    (explore-ind : ExploreInd m explore) where
  open Explorableₘₚ explore-ind
  open ExplorePlug

  explore∘-plug : (M : Monoid m m) → ExplorePlug M explore
  explore∘-plug M = explore-ind $kit plugKit M

  explore-endo-monoid-spec : ∀ (M : Monoid _ m) →
                      let open Mon M in
                      (f : A → C) → with-monoid M f ≈ with-endo-monoid M f
  explore-endo-monoid-spec M f =
           proj₂ (explore-ind
                     (λ e → ExplorePlug M e × e ε _∙_ f ≈ explore-endo e ε _∙_ f)
                     ((const (proj₁ identity)) , refl)
                     (λ {e} {s'} Ps Ps' →
                        P∙ {e} {s'} (proj₁ Ps) (proj₁ Ps')
                      , trans (∙-cong (proj₂ Ps) (proj₂ Ps')) (proj₁ Ps f _))
                     (λ x → Pf x , sym (proj₂ identity _)))
                        where open Mon M
                              open ExploreIndKit (plugKit M)

  explore∘-ind : ∀ (M : Monoid m m) → BigOpMonInd m M (with-endo-monoid M)
  explore∘-ind M P Pε P∙ Pf P≈ =
    proj₂ (explore-ind (λ e → ExplorePlug M e × P (λ f → e id _∘′_ (_∙_ ∘ f) ε))
               (const (proj₁ identity) , Pε)
               (λ {e} {s'} Ps Ps' → ExploreIndKit.P∙ (plugKit M) {e} {s'} (proj₁ Ps) (proj₁ Ps')
                                  , P≈ (λ f → proj₁ Ps f _) (P∙ (proj₂ Ps) (proj₂ Ps')))
               (λ x → ExploreIndKit.Pf (plugKit M) x
                    , P≈ (λ f → sym (proj₂ identity _)) (Pf x)))
    where open Mon M

  explore-ext : ExploreExt explore
  explore-ext ε op = explore-ind (λ e → e _ _ _ ≡ e _ _ _) ≡.refl (≡.ap₂ op)

  ⟦explore⟧ᵤ : ∀ {Aᵣ : A → A → ★_ _}
               (Aᵣ-refl : Reflexive Aᵣ)
              → ⟦Explore⟧ᵤ _ _ m Aᵣ explore explore
  ⟦explore⟧ᵤ Aᵣ-refl Mᵣ zᵣ ∙ᵣ fᵣ = explore-ind (λ e → Mᵣ (e _ _ _) (e _ _ _)) zᵣ (λ η → ∙ᵣ η) (λ η → fᵣ Aᵣ-refl)

  explore-ε : Exploreε m m explore
  explore-ε M = explore-ind (λ e → e ε _ (const ε) ≈ ε)
                            refl
                            (λ x≈ε y≈ε → trans (∙-cong x≈ε y≈ε) (proj₁ identity ε))
                            (λ _ → refl)
    where open Mon M

  explore-hom : ExploreHom m m explore
  explore-hom cm f g = explore-ind (λ e → e _ _ (f ∙° g) ≈ e _ _ f ∙ e _ _ g)
                                   (sym (proj₁ identity ε))
                                   (λ p₀ p₁ → trans (∙-cong p₀ p₁) (∙-interchange _ _ _ _))
                                   (λ _ → refl)
    where open CMon cm

  explore-linˡ : ExploreLinˡ m m explore
  explore-linˡ m _◎_ f k ide dist = explore-ind (λ e → e ε _∙_ (λ x → k ◎ f x) ≈ k ◎ e ε _∙_ f) (sym ide) (λ x x₁ → trans (∙-cong x x₁) (sym (dist k _ _))) (λ x → refl)
    where open Mon m

  explore-linʳ : ExploreLinʳ m m explore
  explore-linʳ m _◎_ f k ide dist = explore-ind (λ e → e ε _∙_ (λ x → f x ◎ k) ≈ e ε _∙_ f ◎ k) (sym ide) (λ x x₁ → trans (∙-cong x x₁) (sym (dist k _ _))) (λ x → refl)
    where open Mon m

  lift-hom-≡ :
      ∀ {S T}
        (zero : S)
        (_+_  : Op₂ S)
        (one  : T)
        (_*_  : Op₂ T)
        (f    : S → T)
        (g    : A → S)
        (hom-0-1 : f zero ≡ one)
        (hom-+-* : ∀ x y → f (x + y) ≡ f x * f y)
      → f (explore zero _+_ g) ≡ explore one _*_ (f ∘ g)
  lift-hom-≡ z _+_ o _*_ = LiftHom.lift-hom _≡_ ≡.refl ≡.trans z _+_ o _*_ (≡.ap₂ _*_)

module Explorable₀
    {A}
    {explore     : Explore₀ A}
    (explore-ind : ExploreInd₀ explore) where
  open Explorableₘₚ explore-ind public
  open Explorableₘ  explore-ind public
  open FromExplore₀ explore     public

  ⟦explore⟧' : ∀ {Aᵣ : A → A → ★_ _}
               (Aᵣ-refl : Reflexive Aᵣ)
              → ⟦Explore⟧ Aᵣ explore explore
  ⟦explore⟧' = ⟦explore⟧ᵤ

  sum-ind : SumInd sum
  sum-ind P P0 P+ Pf = explore-ind (λ e → P (e 0 _+_)) P0 P+ Pf

  sum-ext : SumExt sum
  sum-ext = explore-ext 0 _+_

  sum-zero : SumZero sum
  sum-zero = explore-ε ℕ+.monoid

  sum-hom : SumHom sum
  sum-hom = explore-hom ℕ°.+-commutativeMonoid

  sum-mono : SumMono sum
  sum-mono = explore-mono _≤_ z≤n _+-mono_

  sum-swap' : SumSwap sum
  sum-swap' {sᴮ = sᴮ} sᴮ-0 hom f =
    sum-ind (λ s → s (sᴮ ∘ f) ≡ sᴮ (s ∘ flip f))
            (≡.sym sᴮ-0)
            (λ p q → ≡.trans (≡.ap₂ _+_ p q) (≡.sym (hom _ _))) (λ _ → ≡.refl)
  
  sum-lin : SumLin sum
  sum-lin f zero    = sum-zero
  sum-lin f (suc k) = ≡.trans (sum-hom f (λ x → k * f x)) (≡.ap₂ _+_ (≡.refl {x = sum f}) (sum-lin f k))
  
  sum-const : SumConst sum
  sum-const x = ≡.trans (≡.trans (sum-ext (λ _ → ≡.sym (proj₂ ℕ°.*-identity x))) (sum-lin (const 1) x)) (ℕ°.*-comm x Card)
  
  sumStableUnder : ∀ {p} → StableUnder explore p → SumStableUnder sum p
  sumStableUnder SU-p = SU-p 0 _+_

  count-ext : CountExt count
  count-ext f≗g = sum-ext (≡.cong 𝟚▹ℕ ∘ f≗g)

  countStableUnder : ∀ {p} → SumStableUnder sum p → CountStableUnder count p
  countStableUnder sumSU-p f = sumSU-p (𝟚▹ℕ ∘ f)

  diff-list = with-endo-monoid (List.monoid A) List.[_]

  list≡diff-list : list ≡ diff-list
  list≡diff-list = explore-endo-monoid-spec (List.monoid A) List.[_]

module Adequate-sum₀
  {{_ : UA}}{{_ : FunExt}}
  {A}{B}
  {sumᴬ : Sum A}{sumᴮ : Sum B}
  (sumᴬ-adq : Adequate-sum sumᴬ)
  (sumᴮ-adq : Adequate-sum sumᴮ) where

  open ≡
  sumStableUnder : (p : A ≃ B)(f : A → ℕ)
                 → sumᴬ f ≡ sumᴮ (f ∘ <– p)
  sumStableUnder p f = Fin-injective (sumᴬ-adq f
                                      ∙ Σ-fst≃′ p _
                                      ∙ ! sumᴮ-adq (f ∘ <– p))


module EndoAdequate-sum₀
  {{_ : UA}}{{_ : FunExt}}
  {A}
  {sum : Sum A}
  (sum-adq : Adequate-sum sum) where

  open Adequate-sum₀ sum-adq sum-adq public
  open ≡

  module _ (p q : A → 𝟚)(prf : sum (𝟚▹ℕ ∘ p) ≡ sum (𝟚▹ℕ ∘ q)) where
    private

        P = λ x → p x ≡ 1₂
        Q = λ x → q x ≡ 1₂
        ¬P = λ x → p x ≡ 0₂
        ¬Q = λ x → q x ≡ 0₂

        π : Σ A P ≡ Σ A Q
        π = ! Σ=′ _ (count-≡ p)
            ∙ ! (sum-adq (𝟚▹ℕ ∘ p))
            ∙ ap Fin prf
            ∙ sum-adq (𝟚▹ℕ ∘ q)
            ∙ Σ=′ _ (count-≡ q)
        
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
        
        lemma1 : ∀ px qx → (qx ≡ 1₂) ≡ (Fin (𝟚▹ℕ (px ∧ qx)) ⊎ (px ≡ 0₂ × qx ≡ 1₂))
        lemma1 px qx = ! Fin-≡-≡1₂ qx
                     ∙ ap Fin (lem1 px qx)
                     ∙ ! Fin-⊎-+
                     ∙ ⊎= refl (! Fin-×-* ∙ ×= (Fin-≡-≡0₂ px) (Fin-≡-≡1₂ qx))

        lemma2 : ∀ px qx → (Fin (𝟚▹ℕ (px ∧ qx)) ⊎ (px ≡ 1₂ × qx ≡ 0₂)) ≡ (px ≡ 1₂)
        lemma2 px qx = ! ⊎= refl (! Fin-×-* ∙ ×= (Fin-≡-≡1₂ px) (Fin-≡-≡0₂ qx)) ∙ Fin-⊎-+ ∙ ap Fin (! lem2 px qx) ∙ Fin-≡-≡1₂ px
  
        π' : (Fin (sum (λ x → 𝟚▹ℕ (p x ∧ q x))) ⊎ Σ A (λ x →  P x × ¬Q x))
           ≡ (Fin (sum (λ x → 𝟚▹ℕ (p x ∧ q x))) ⊎ Σ A (λ x → ¬P x ×  Q x))
        π' = ⊎= (sum-adq (λ x → 𝟚▹ℕ (p x ∧ q x))) refl
           ∙ ! Σ⊎-split
           ∙ Σ=′ _ (λ x → lemma2 (p x) (q x))
           ∙ π
           ∙ Σ=′ _ (λ x → lemma1 (p x) (q x))
           ∙ Σ⊎-split
           ∙ ! ⊎= (sum-adq (λ x → 𝟚▹ℕ (p x ∧ q x))) refl

        π'' : Σ A (P ×° ¬Q) ≡ Σ A (¬P ×° Q)
        π'' = Fin⊎-injective (sum (λ x → 𝟚▹ℕ (p x ∧ q x))) π'
  
        module M = EquivalentSubsets π''
    
--    indIso : A ≡ A
--    indIso = equiv M.π M.π M.ππ M.ππ
      
    indIsIso : p ≡ q ∘ M.π
    indIsIso = M.prop
  
module Explorableₛ {ℓ A} {exploreₛ : Explore (ₛ ℓ) A}
                   (explore-ind : ExploreInd ℓ exploreₛ) where
  open Explorableₘₚ explore-ind

  reify : Reify exploreₛ
  reify = explore-ind (λ eᴬ → Πᵉ eᴬ _) _ _,_

  module _ (P : A → ★_ ℓ) where
     open LiftHom {★_ ℓ} {★_ ℓ} (λ A B → B → A) id _∘′_
                  (Lift 𝟘) _⊎_ (Lift 𝟙) _×_
                  (λ f g → ×-map f g) Dec P (const (no (λ{ (lift ()) })))
                  (λ _ _ → uncurry Dec-⊎)
                  public renaming (lift-hom to lift-Dec)

module Explorable₁ {A} {explore : Explore ₁ A}
                   (explore-ind : ExploreInd ₁ explore) where
  open Explorableₘₚ explore-ind public

  lift+ : ∀ {ℓ} → Lift {ℓ = ℓ} ℕ → Lift {ℓ = ℓ} ℕ → Lift {ℓ = ℓ} ℕ
  lift+ (lift x) (lift y) = lift (x + y)

  open ≡
  foo : ∀ {{_ : UA}}(f : A → ℕ) → Fin (lower (explore (lift 0) lift+ (lift ∘ f))) ≡ Σᵉ explore (Fin ∘ f)
  foo f = LiftHom.lift-hom _≡_ ≡.refl ≡.trans (lift 0) lift+ (Lift 𝟘) _⊎_ ⊎= (Fin ∘ lower) (lift ∘ f) (Fin0≡𝟘 ∙ ! Lift≡id) (λ _ _ → ! Fin-⊎-+)

module Explorable₀₁
          {{_ : UA}}
          {A}
          (e₀ : Explore ₀ A)
          (e₁ : Explore ₁ A)
          (eᵣ : ⟦Explore⟧ᵤ ₀ ₁ ₁ _≡_ e₀ e₁)
          where
  open ≡
  module _ (f : A → ℕ) where
    sum⇒Σᵉ : Fin (e₀ 0 _+_ f) ≡ e₁ (Lift 𝟘) _⊎_ (Fin ∘ f)
    sum⇒Σᵉ = eᵣ (λ n X → Fin n ≡ X)
                (Fin0≡𝟘 ∙ ! Lift≡id)
                (λ p q → ! Fin-⊎-+ ∙ ⊎= p q)
                (ap (Fin ∘ f))

    product⇒Πᵉ : Fin (e₀ 1 _*_ f) ≡ e₁ (Lift 𝟙) _×_ (Fin ∘ f)
    product⇒Πᵉ = eᵣ (λ n X → Fin n ≡ X)
                    (Fin1≡𝟙 ∙ ! Lift≡id)
                    (λ p q → ! Fin-×-* ∙ ×= p q)
                    (ap (Fin ∘ f))

  module _ (f : A → 𝟚) where
    all⇒Πᵉ : ✓ (e₀ 1₂ _∧_ f) ≡ e₁ (Lift 𝟙) _×_ (✓ ∘ f)
    all⇒Πᵉ = eᵣ (λ b X → ✓ b ≡ X)
                (! Lift≡id)
                (λ p q → ✓-∧-× _ _ ∙ ×= p q)
                (ap (✓ ∘ f))

module Explorableₛₛ {ℓ A} {exploreₛ : Explore (ₛ ℓ) A}
                    (explore-indₛ : ExploreInd (ₛ ℓ) exploreₛ) where

  unfocus : Unfocus exploreₛ
  unfocus = explore-indₛ Unfocus (λ{ (lift ()) }) (λ P Q → [ P , Q ]) (λ η → _,_ η)

module ExplorableRecord where
    record Explorable A : ★₁ where
      constructor mk
      field
        explore     : Explore₀ A
        explore-ind : ExploreInd₀ explore

      open Explorable₀ explore-ind
      field
        adequate-sum     : Adequate-sum sum
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
                       (0′  : X)
                       (_+_ : X → X → X)
                       (_*_ : X → X → X) where

      Σᴮ = explore μB 0′ _+_
      Π' = explore μA 0′ _*_
      Σ' = explore (μA→ μB) 0′ _+_

      DistFun = ∀ f → Π' (Σᴮ ∘ f) ≈ Σ' (Π' ∘ _ˢ_ f)

    DistFun : ∀ {A} → Explorable A → ExploreForFun A → ★₁
    DistFun μA μA→ = ∀ {B} (μB : Explorable B) c → let open CMon {₀}{₀} c in
                       ∀ _*_ → Zero _≈_ ε _*_ → _DistributesOver_ _≈_ _*_ _∙_ → _*_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
                       → DistFun.DistFun μA μA→ μB _≈_ ε _∙_ _*_

    DistFunable : ∀ {A} → Funable A → ★₁
    DistFunable (μA , μA→) = DistFun μA μA→

    module _ {{_ : UA}}{{_ : FunExt}} where
        μ-iso : ∀ {A B} → (A ≃ B) → Explorable A → Explorable B
        μ-iso {A}{B} A≃B μA = mk (EM.map _ A→B (explore μA)) (EM.map-ind _ A→B (explore-ind μA)) ade
          where
            open ≡
            A→B = –> A≃B
            ade = λ f → adequate-sum μA (f ∘ A→B) ∙ Σ-fst≃ A≃B _

        -- I guess this could be more general
        μ-iso-preserve : ∀ {A B} (A≃B : A ≃ B) f (μA : Explorable A) → sum μA f ≡ sum (μ-iso A≃B μA) (f ∘ <– A≃B)
        μ-iso-preserve A≃B f μA = sum-ext μA (λ x → ap f (! (<–-inv-l A≃B x)))
          where open ≡

          {-
        μLift : ∀ {A} → Explorable A → Explorable (Lift A)
        μLift = μ-iso {!(! Lift↔id)!}
          where open ≡
          -}

    explore-swap' : ∀ {A B} cm (μA : Explorable A) (μB : Explorable B) f →
                   let open CMon cm
                       eᴬ = explore μA ε _∙_
                       eᴮ = explore μB ε _∙_ in
                   eᴬ (eᴮ ∘ f) ≈ eᴮ (eᴬ ∘ flip f)
    explore-swap' cm μA μB = explore-swap μA m (explore-ε μB m) (explore-hom μB cm)
      where open CMon cm

    sum-swap : ∀ {A B} (μA : Explorable A) (μB : Explorable B) f →
               sum μA (sum μB ∘ f) ≡ sum μB (sum μA ∘ flip f)
    sum-swap = explore-swap' ℕ°.+-commutativeMonoid

module ExplorablePoly
    {A}
    {explore     : ∀ {m} → Explore m A}
    (explore-ind : ∀ {p m} → ExploreInd p {m} explore)
    (exploreᵣ    : ∀ {a₀ a₁ aᵣ} → ⟦Explore⟧ᵤ a₀ a₁ aᵣ _≡_ explore explore)
    (adequate-Σᵉ : ∀ {ℓ} → Adequate-Σᵉ {ℓ} explore)
    (adequate-Πᵉ : ∀ {ℓ} → Adequate-Πᵉ {ℓ} explore)
    where
  open FromExplore₀ explore public
  module E₀₁ {{_ : UA}} = Explorable₀₁ explore explore (exploreᵣ {₀} {₁} {₁})
  open ≡

  unfocus : ∀ {ℓ} → Unfocus {ℓ} explore
  unfocus = Explorableₛₛ.unfocus explore-ind

  module _ {{_ : UA}} (f : A → ℕ) where
      adequate-sum : Fin (sum f) ≡ Σ A (Fin ∘ f)
      adequate-sum = E₀₁.sum⇒Σᵉ f ∙ adequate-Σᵉ (Fin ∘ f)

      adequate-product : Fin (product f) ≡ Π A (Fin ∘ f)
      adequate-product = E₀₁.product⇒Πᵉ f ∙ adequate-Πᵉ (Fin ∘ f)

  module _ {{_ : UA}} (f : A → 𝟚) where
      lift-all : ✓ (all f) ≡ (∀ x → ✓ (f x))
      lift-all = E₀₁.all⇒Πᵉ f ∙ adequate-Πᵉ _

      check! : {pf : ✓ (all f)} → (∀ x → ✓ (f x))
      check! {pf} = coe lift-all pf
-- -}
-- -}
-- -}
-- -}
