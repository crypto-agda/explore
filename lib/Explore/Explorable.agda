{-# OPTIONS --without-K #-}
-- Constructions on top of exploration functions

open import Level.NP
open import Type hiding (★)
open import Type.Identities
open import Function.NP
open import Function.Extensionality
open import Algebra.FunctionProperties.NP
open import Data.Two.Base
open import Data.Indexed
open import Data.Nat.NP hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Maybe.NP
open import Algebra
open import Data.Product.NP renaming (map to ×-map) hiding (first)
open import Data.Sum.NP
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

module _ {m a} {A : ★ a} where
  open EM {a} m
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

private
  module FindForward {a} {A : ★ a} (explore : Explore a A) where
    find? : Find? A
    find? = explore nothing (M?._∣_ _)

    first : Maybe A
    first = find? just

    findKey : FindKey A
    findKey pred = find? (λ x → [0: nothing 1: just x ] (pred x))

module ExplorePlug {ℓ a} {A : ★ a} where
  record ExploreIndKit p (P : Explore ℓ A → ★ p) : ★ (a ⊔ ₛ ℓ ⊔ p) where
    constructor mk
    field
      Pε : P empty-explore
      P∙ : ∀ {e₀ e₁ : Explore ℓ A} → P e₀ → P e₁ → P (merge-explore e₀ e₁)
      Pf : ∀ x → P (point-explore x)

  _$kit_ : ∀ {p} {P : Explore ℓ A → ★ p} {e : Explore ℓ A}
           → ExploreInd p e → ExploreIndKit p P → P e
  _$kit_ {P = P} ind (mk Pε P∙ Pf) = ind P Pε P∙ Pf

  _,-kit_ : ∀ {p} {P : Explore ℓ A → ★ p}{Q : Explore ℓ A → ★ p}
            → ExploreIndKit p P → ExploreIndKit p Q → ExploreIndKit p (P ×° Q)
  Pk ,-kit Qk = mk (Pε Pk , Pε Qk)
                   (λ x y → P∙ Pk (fst x) (fst y) , P∙ Qk (snd x) (snd y))
                   (λ x → Pf Pk x , Pf Qk x)
               where open ExploreIndKit

  ExploreInd-Extra : ∀ p → Explore ℓ A → ★ _
  ExploreInd-Extra p exp =
    ∀ (Q     : Explore ℓ A → ★ p)
      (Q-kit : ExploreIndKit p Q)
      (P     : Explore ℓ A → ★ p)
      (Pε    : P empty-explore)
      (P∙    : ∀ {e₀ e₁ : Explore ℓ A} → Q e₀ → Q e₁ → P e₀ → P e₁
               → P (merge-explore e₀ e₁))
      (Pf    : ∀ x → P (point-explore x))
    → P exp

  to-extra : ∀ {p} {e : Explore ℓ A} → ExploreInd p e → ExploreInd-Extra p e
  to-extra e-ind Q Q-kit P Pε P∙ Pf =
   snd (e-ind (Q ×° P)
           (Qε , Pε)
           (λ { (a , b) (c , d) → Q∙ a c , P∙ a c b d })
           (λ x → Qf x , Pf x))
   where open ExploreIndKit Q-kit renaming (Pε to Qε; P∙ to Q∙; Pf to Qf)

  ExplorePlug : ∀ {m} (M : Monoid ℓ m) (e : Explore _ A) → ★ _
  ExplorePlug M e = ∀ f x → e∘ ε _∙_ f ∙ x ≈ e∘ x _∙_ f
     where open Mon M
           e∘ = explore-endo e

  plugKit : ∀ {m} (M : Monoid ℓ m) → ExploreIndKit _ (ExplorePlug M)
  plugKit M = mk (λ _ → fst identity)
                 (λ Ps Ps' f x →
                    trans (∙-cong (! Ps _ _) refl)
                          (trans (assoc _ _ _)
                                 (trans (∙-cong refl (Ps' _ x)) (Ps _ _))))
                 (λ x f _ → ∙-cong (snd identity (f x)) refl)
       where open Mon M

module FromExplore
    {a} {A : ★ a}
    (explore : ∀ {ℓ} → Explore ℓ A) where

  module _ {ℓ} where
    with-monoid : ∀ {m} → ExploreMon ℓ m A
    with-monoid = explore-monoid explore

    with∘ : Explore ℓ A
    with∘ = explore-endo explore

    with-endo-monoid : ∀ {m} → ExploreMon ℓ m A
    with-endo-monoid = explore-endo-monoid explore

    backward : Explore ℓ A
    backward = explore-backward explore

    gfilter : ∀ {B} → (A →? B) → Explore ℓ B
    gfilter f = gfilter-explore f explore

    filter : (A → 𝟚) → Explore ℓ A
    filter p = filter-explore p explore

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

module FromExploreInd
    {a} {A : ★ a}
    {explore : ∀ {ℓ} → Explore ℓ A}
    (explore-ind : ∀ {p ℓ} → ExploreInd {ℓ} p explore)
    where

  open FromExplore explore public

  module _ {ℓ p} where
    explore-mon-ext : ExploreMonExt {ℓ} p explore
    explore-mon-ext m {f} {g} f≈°g = explore-ind (λ s → s _ _ f ≈ s _ _ g) refl ∙-cong f≈°g
      where open Mon m

    explore-mono : ExploreMono {ℓ} p explore
    explore-mono _⊆_ z⊆ _∙-mono_ {f} {g} f⊆°g =
      explore-ind (λ e → e _ _ f ⊆ e _ _ g) z⊆ _∙-mono_ f⊆°g

    open ExplorePlug {ℓ} {a} {A}

    explore∘-plug : (M : Monoid ℓ ℓ) → ExplorePlug M explore
    explore∘-plug M = explore-ind $kit plugKit M

    module _ (M : Monoid ℓ ℓ)
             (open Mon M)
             (f : A → C)
             where
        explore-endo-monoid-spec′ : ∀ z → explore ε _∙_ f ∙ z ≈ explore-endo explore z _∙_ f
        explore-endo-monoid-spec′ = explore-ind (λ e → ∀ z → e ε _∙_ f ∙ z ≈ explore-endo e z _∙_ f)
                                                (fst identity) (λ P₀ P₁ z → trans (assoc _ _ _) (trans (∙-cong refl (P₁ z)) (P₀ _))) (λ _ _ → refl)

        explore-endo-monoid-spec : with-monoid M f ≈ with-endo-monoid M f
        explore-endo-monoid-spec = trans (! snd identity _) (explore-endo-monoid-spec′ ε)

    explore∘-ind : ∀ (M : Monoid ℓ ℓ) → BigOpMonInd ℓ M (with-endo-monoid M)
    explore∘-ind M P Pε P∙ Pf P≈ =
      snd (explore-ind (λ e → ExplorePlug M e × P (λ f → e id _∘′_ (_∙_ ∘ f) ε))
                 (const (fst identity) , Pε)
                 (λ {e} {s'} Ps Ps' → ExploreIndKit.P∙ (plugKit M) {e} {s'} (fst Ps) (fst Ps')
                                    , P≈ (λ f → fst Ps f _) (P∙ (snd Ps) (snd Ps')))
                 (λ x → ExploreIndKit.Pf (plugKit M) x
                      , P≈ (λ f → ! snd identity _) (Pf x)))
      where open Mon M

    explore-swap : ∀ {b} → ExploreSwap {ℓ} p explore {b}
    explore-swap mon {eᴮ} eᴮ-ε pf f =
      explore-ind (λ e → e _ _ (eᴮ ∘ f) ≈ eᴮ (e _ _ ∘ flip f))
                  (! eᴮ-ε)
                  (λ p q → trans (∙-cong p q) (! pf _ _))
                  (λ _ → refl)
      where open Mon mon

    explore-ε : Exploreε {ℓ} p explore
    explore-ε M = explore-ind (λ e → e ε _ (const ε) ≈ ε)
                              refl
                              (λ x≈ε y≈ε → trans (∙-cong x≈ε y≈ε) (fst identity ε))
                              (λ _ → refl)
      where open Mon M

    explore-hom : ExploreHom {ℓ} p explore
    explore-hom cm f g = explore-ind (λ e → e _ _ (f ∙° g) ≈ e _ _ f ∙ e _ _ g)
                                     (! fst identity ε)
                                     (λ p₀ p₁ → trans (∙-cong p₀ p₁) (∙-interchange _ _ _ _))
                                     (λ _ → refl)
      where open CMon cm

    explore-linˡ : ExploreLinˡ {ℓ} p explore
    explore-linˡ m _◎_ f k ide dist = explore-ind (λ e → e ε _∙_ (λ x → k ◎ f x) ≈ k ◎ e ε _∙_ f) (! ide) (λ x x₁ → trans (∙-cong x x₁) (! dist k _ _)) (λ x → refl)
      where open Mon m

    explore-linʳ : ExploreLinʳ {ℓ} p explore
    explore-linʳ m _◎_ f k ide dist = explore-ind (λ e → e ε _∙_ (λ x → f x ◎ k) ≈ e ε _∙_ f ◎ k) (! ide) (λ x x₁ → trans (∙-cong x x₁) (! dist k _ _)) (λ x → refl)
      where open Mon m

    module ProductMonoid
        {M : ★₀} (εₘ : M) (_⊕ₘ_ : Op₂ M)
        {N : ★₀} (εₙ : N) (_⊕ₙ_ : Op₂ N)
        where
        ε = (εₘ , εₙ)
        _⊕_ : Op₂ (M × N)
        (xₘ , xₙ) ⊕ (yₘ , yₙ) = (xₘ ⊕ₘ yₘ , xₙ ⊕ₙ yₙ)

        explore-product-monoid :
          ∀ fₘ fₙ → explore ε _⊕_ < fₘ , fₙ > ≡ (explore εₘ _⊕ₘ_ fₘ , explore εₙ _⊕ₙ_ fₙ)
        explore-product-monoid fₘ fₙ =
          explore-ind (λ e → e ε _⊕_ < fₘ , fₙ > ≡ (e εₘ _⊕ₘ_ fₘ , e εₙ _⊕ₙ_ fₙ)) ≡.refl (≡.ap₂ _⊕_) (λ _ → ≡.refl)
  {-
  empty-explore:
    ε ≡ (εₘ , εₙ) ✓
  point-explore (x , y):
    < fₘ , fₙ > (x , y) ≡ (fₘ x , fₙ y) ✓
  merge-explore e₀ e₁:
    e₀ ε _⊕_ < fₘ , fₙ > ⊕ e₁ ε _⊕_ < fₘ , fₙ >
    ≡
    (e₀ εₘ _⊕ₘ_ fₘ , e₀ εₙ _⊕ₙ_ fₙ) ⊕ (e₁ εₘ _⊕ₘ_ fₘ , e₁ εₙ _⊕ₙ_ fₙ)
    ≡
    (e₀ εₘ _⊕ₘ_ fₘ ⊕ e₁ εₘ _⊕ₘ_ fₘ , e₀ εₙ _⊕ₙ_ fₙ ⊕ e₁ εₙ _⊕ₙ_ fₙ)
  -}

  module _ {ℓ} where
    reify : Reify {ℓ} explore
    reify = explore-ind (λ eᴬ → Πᵉ eᴬ _) _ _,_

    unfocus : Unfocus {ℓ} explore
    unfocus = explore-ind Unfocus (λ{ (lift ()) }) (λ P Q → [ P , Q ]) (λ η → _,_ η)

    module _ {ℓᵣ aᵣ} {Aᵣ : A → A → ★ aᵣ}
             (Aᵣ-refl : Reflexive Aᵣ) where
      ⟦explore⟧ : ⟦Explore⟧ ℓᵣ Aᵣ (explore {ℓ}) (explore {ℓ})
      ⟦explore⟧ Mᵣ zᵣ ∙ᵣ fᵣ = explore-ind (λ e → Mᵣ (e _ _ _) (e _ _ _)) zᵣ (λ η → ∙ᵣ η) (λ η → fᵣ Aᵣ-refl)

    explore-ext : ExploreExt {ℓ} explore
    explore-ext ε op = explore-ind (λ e → e _ _ _ ≡ e _ _ _) ≡.refl (≡.ap₂ op)

  module LiftHom
       {m p}
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
       (hom-+-* : ∀ {x y} → (f (x + y)) ≈ (f x * f y))
       where

        lift-hom : f (explore zero _+_ g) ≈ explore one _*_ (f ∘ g)
        lift-hom = explore-ind (λ e → f (e zero _+_ g) ≈ e one _*_ (f ∘ g))
                               hom-0-1
                               (λ p q → ≈-trans hom-+-* (≈-cong-* p q))
                               (λ _ → ≈-refl)

  module _ {ℓ} {P : A → ★_ ℓ} where
    open LiftHom {S = ★_ ℓ} {★_ ℓ} (λ A B → B → A) id _∘′_
                 (Lift 𝟘) _⊎_ (Lift 𝟙) _×_
                 (λ f g → ×-map f g) Dec P (const (no (λ{ (lift ()) })))
                 (uncurry Dec-⊎)
                 public renaming (lift-hom to lift-Dec)

  module FromFocus {p} (focus : Focus {p} explore) where
    Dec-Σ : ∀ {P} → Π A (Dec ∘ P) → Dec (Σ A P)
    Dec-Σ = map-Dec unfocus focus ∘ lift-Dec ∘ reify

  lift-hom-≡ :
      ∀ {m} {S T : ★ m}
        (zero : S)
        (_+_  : Op₂ S)
        (one  : T)
        (_*_  : Op₂ T)
        (f    : S → T)
        (g    : A → S)
        (hom-0-1 : f zero ≡ one)
        (hom-+-* : ∀ {x y} → f (x + y) ≡ f x * f y)
      → f (explore zero _+_ g) ≡ explore one _*_ (f ∘ g)
  lift-hom-≡ z _+_ o _*_ = LiftHom.lift-hom _≡_ ≡.refl ≡.trans z _+_ o _*_ (≡.ap₂ _*_)

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
  sum-swap' {sumᴮ = sᴮ} sᴮ-0 hom f =
    sum-ind (λ s → s (sᴮ ∘ f) ≡ sᴮ (s ∘ flip f))
            (! sᴮ-0)
            (λ p q → (ap₂ _+_ p q) ∙ (! hom _ _)) (λ _ → refl)
    where open ≡

  sum-lin : SumLin sum
  sum-lin f zero    = sum-zero
  sum-lin f (suc k) = ≡.trans (sum-hom f (λ x → k * f x)) (≡.ap₂ _+_ (≡.refl {x = sum f}) (sum-lin f k))

  sum-const : SumConst sum
  sum-const x = sum-ext (λ _ → ! snd ℕ°.*-identity x) ∙ sum-lin (const 1) x ∙ ℕ°.*-comm x Card
    where open ≡

  exploreStableUnder→sumStableUnder : ∀ {p} → StableUnder explore p → SumStableUnder sum p
  exploreStableUnder→sumStableUnder SU-p = SU-p 0 _+_

  count-ext : CountExt count
  count-ext f≗g = sum-ext (≡.cong 𝟚▹ℕ ∘ f≗g)

  sumStableUnder→countStableUnder : ∀ {p} → SumStableUnder sum p → CountStableUnder count p
  sumStableUnder→countStableUnder sumSU-p f = sumSU-p (𝟚▹ℕ ∘ f)

  diff-list = with-endo-monoid (List.monoid A) List.[_]

  {-
  list≡diff-list : list ≡ diff-list
  list≡diff-list = {!explore-endo-monoid-spec (List.monoid A) List.[_]!}
  -}

  lift-op₂ : ∀ {a}{A : ★_ a}(op : Op₂ A){ℓ} → Lift {ℓ = ℓ} A → Lift {ℓ = ℓ} A → Lift {ℓ = ℓ} A
  lift-op₂ op (lift x) (lift y) = lift (op x y)

  lift-sum : ∀ ℓ → Sum A
  lift-sum ℓ f = lower {₀} {ℓ} (explore (lift 0) (lift-op₂ _+_) (lift ∘ f))

  Fin-lower-sum≡Σᵉ-Fin : ∀ {{_ : UA}}(f : A → ℕ) → Fin (lift-sum _ f) ≡ Σᵉ explore (Fin ∘ f)
  Fin-lower-sum≡Σᵉ-Fin f = LiftHom.lift-hom _≡_ ≡.refl ≡.trans (lift 0) (lift-op₂ _+_) (Lift 𝟘) _⊎_ ⊎= (Fin ∘ lower) (lift ∘ f) (Fin0≡𝟘 ∙ ! Lift≡id) (! Fin-⊎-+)
    where open ≡

module FromTwoExploreInd
    {a} {A : ★ a}
    {eᴬ : ∀ {ℓ} → Explore ℓ A}
    (eᴬ-ind : ∀ {p ℓ} → ExploreInd {ℓ} p eᴬ)
    {b} {B : ★ b}
    {eᴮ : ∀ {ℓ} → Explore ℓ B}
    (eᴮ-ind : ∀ {p ℓ} → ExploreInd {ℓ} p eᴮ)
    where

    module A = FromExploreInd eᴬ-ind
    module B = FromExploreInd eᴮ-ind

    module _ {c ℓ}(cm : CommutativeMonoid c ℓ) where
        open CMon cm

        opᴬ = eᴬ ε _∙_
        opᴮ = eᴮ ε _∙_

        -- TODO use lift-hom
        explore-swap' : ∀ f → opᴬ (opᴮ ∘ f) ≈ opᴮ (opᴬ ∘ flip f)
        explore-swap' = A.explore-swap m (B.explore-ε m) (B.explore-hom cm)

    sum-swap : ∀ f → A.sum (B.sum ∘ f) ≡ B.sum (A.sum ∘ flip f)
    sum-swap = explore-swap' ℕ°.+-commutativeMonoid

module FromTwoAdequate-sum
  {{_ : UA}}{{_ : FunExt}}
  {A}{B}
  {sumᴬ : Sum A}{sumᴮ : Sum B}
  (open Adequacy _≡_)
  (sumᴬ-adq : Adequate-sum sumᴬ)
  (sumᴮ-adq : Adequate-sum sumᴮ) where

  open ≡
  sumStableUnder : (p : A ≃ B)(f : B → ℕ)
                 → sumᴬ (f ∘ ·→ p) ≡ sumᴮ f
  sumStableUnder p f = Fin-injective (sumᴬ-adq (f ∘ ·→ p)
                                      ∙ Σ-fst≃ p _
                                      ∙ ! sumᴮ-adq f)

  sumStableUnder′ : (p : A ≃ B)(f : A → ℕ)
                 → sumᴬ f ≡ sumᴮ (f ∘ <– p)
  sumStableUnder′ p f = Fin-injective (sumᴬ-adq f
                                      ∙ Σ-fst≃′ p _
                                      ∙ ! sumᴮ-adq (f ∘ <– p))

module FromAdequate-sum
  {A}
  {sum : Sum A}
  (open Adequacy _≡_)
  (sum-adq : Adequate-sum sum)
  {{_ : UA}}{{_ : FunExt}}
  where

  open FromTwoAdequate-sum sum-adq sum-adq public
  open ≡

  private
    count : Count A
    count f = sum (𝟚▹ℕ ∘ f)

  private
    module M {p q : A → 𝟚}(same-count : count p ≡ count q) where
      private

        P = λ x → p x ≡ 1₂
        Q = λ x → q x ≡ 1₂
        ¬P = λ x → p x ≡ 0₂
        ¬Q = λ x → q x ≡ 0₂

        π : Σ A P ≡ Σ A Q
        π = ! Σ=′ _ (count-≡ p)
            ∙ ! (sum-adq (𝟚▹ℕ ∘ p))
            ∙ ap Fin same-count
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

      open EquivalentSubsets π'' public

  same-count→iso : ∀{p q : A → 𝟚}(same-count : count p ≡ count q) → p ≡ q ∘ M.π {p} {q} same-count
  same-count→iso {p} {q} sc = M.prop {p} {q} sc

module From⟦Explore⟧
    {-a-} {A : ★₀ {- a-}}
    {explore   : ∀ {ℓ} → Explore ℓ A}
    (⟦explore⟧ : ∀ {ℓ₀ ℓ₁} ℓᵣ → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ _≡_ explore explore)
    {{_ : UA}}
    where
  open FromExplore explore

  module AlsoInFromExploreInd
          {ℓ}(M : Monoid ℓ ℓ)
             (open Mon M)
             (f : A → C)
             where
        explore-endo-monoid-spec′ : ∀ z → explore ε _∙_ f ∙ z ≈ explore-endo explore z _∙_ f
        explore-endo-monoid-spec′ = ⟦explore⟧ ₀ {C} {C → C}
                                              (λ r s → ∀ z → r ∙ z ≈ s z)
                                              (fst identity)
                                              (λ P₀ P₁ z → trans (assoc _ _ _) (trans (∙-cong refl (P₁ z)) (P₀ _)))
                                              (λ xᵣ _ → ∙-cong (reflexive (≡.ap f xᵣ)) refl)

        explore-endo-monoid-spec : with-monoid M f ≈ with-endo-monoid M f
        explore-endo-monoid-spec = trans (! snd identity _) (explore-endo-monoid-spec′ ε)

  open ≡
  module _ (f : A → ℕ) where
    sum⇒Σᵉ : Fin (explore 0 _+_ f) ≡ explore (Lift 𝟘) _⊎_ (Fin ∘ f)
    sum⇒Σᵉ = ⟦explore⟧ {₀} {₁} ₁
                (λ n X → Fin n ≡ X)
                (Fin0≡𝟘 ∙ ! Lift≡id)
                (λ p q → ! Fin-⊎-+ ∙ ⊎= p q)
                (ap (Fin ∘ f))

    product⇒Πᵉ : Fin (explore 1 _*_ f) ≡ explore (Lift 𝟙) _×_ (Fin ∘ f)
    product⇒Πᵉ = ⟦explore⟧ {₀} {₁} ₁
                    (λ n X → Fin n ≡ X)
                    (Fin1≡𝟙 ∙ ! Lift≡id)
                    (λ p q → ! Fin-×-* ∙ ×= p q)
                    (ap (Fin ∘ f))

  module _ (f : A → 𝟚) where
    ✓all-Πᵉ : ✓ (all f) ≡ Πᵉ explore (✓ ∘ f)
    ✓all-Πᵉ = ⟦explore⟧ {₀} {₁} ₁
                (λ b X → ✓ b ≡ X)
                (! Lift≡id)
                (λ p q → ✓-∧-× _ _ ∙ ×= p q)
                (ap (✓ ∘ f))

    ✓any→Σᵉ : ✓ (any f) → Σᵉ explore (✓ ∘ f)
    ✓any→Σᵉ p = ⟦explore⟧ {₀} {ₛ ₀} ₁
                         (λ b (X : ★₀) → Lift (✓ b) → X)
                         (λ x → lift (lower x))
                         (λ { {0₂} {x₁} xᵣ {y₀} {y₁} yᵣ zᵣ → inr (yᵣ zᵣ)
                            ; {1₂} {x₁} xᵣ {y₀} {y₁} yᵣ zᵣ → inl (xᵣ _) })
                         (λ xᵣ x → tr (✓ ∘ f) xᵣ (lower x)) (lift p)

  module FromAdequate-Σᵉ
           (adequate-Σᵉ : ∀ {ℓ} → Adequate-Σ {ℓ} (Σᵉ explore))
          where
    open Adequacy

    adequate-sum : Adequate-sum _≡_ sum
    adequate-sum f = sum⇒Σᵉ f ∙ adequate-Σᵉ (Fin ∘ f)

    open FromAdequate-sum adequate-sum public

    adequate-any : Adequate-any -→- any
    adequate-any f e = coe (adequate-Σᵉ (✓ ∘ f)) (✓any→Σᵉ f e)

  module FromAdequate-Πᵉ
           (adequate-Πᵉ : ∀ {ℓ} → Adequate-Π {ℓ} (Πᵉ explore))
          where
    open Adequacy

    adequate-product : Adequate-product _≡_ product
    adequate-product f = product⇒Πᵉ f ∙ adequate-Πᵉ (Fin ∘ f)

    adequate-all : Adequate-all _≡_ all
    adequate-all f = ✓all-Πᵉ f ∙ adequate-Πᵉ _

    check! : (f : A → 𝟚) {pf : ✓ (all f)} → (∀ x → ✓ (f x))
    check! f {pf} = coe (adequate-all f) pf

{-
module ExplorableRecord where
    record Explorable A : ★₁ where
      constructor mk
      field
        explore     : Explore₀ A
        explore-ind : ExploreInd₀ explore

      open FromExploreInd explore-ind
      field
        adequate-sum     : Adequate-sum sum
    --  adequate-product : AdequateProduct product

      open FromExploreInd explore-ind public

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
-- -}
-- -}
-- -}
-- -}
