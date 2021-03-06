{-# OPTIONS --without-K #-}
-- Specific constructions on top of summation functions

module Explore.Summable where

open import Type
open import Function.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_ ; _≗_ ; _≗₂_)
open import Explore.Core
open import Explore.Properties
open import Explore.Product
open import Data.Product
open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Two
open Data.Two.Indexed

module FromSum {a} {A : ★_ a} (sum : Sum A) where
  Card : ℕ
  Card = sum (const 1)

  count : Count A
  count f = sum (𝟚▹ℕ ∘ f)

  sum-lin⇒sum-zero : SumLin sum → SumZero sum
  sum-lin⇒sum-zero sum-lin = sum-lin (λ _ → 0) 0

  sum-mono⇒sum-ext : SumMono sum → SumExt sum
  sum-mono⇒sum-ext sum-mono f≗g = ℕ≤.antisym (sum-mono (ℕ≤.reflexive ∘ f≗g)) (sum-mono (ℕ≤.reflexive ∘ ≡.sym ∘ f≗g))

  sum-ext+sum-hom⇒sum-mono : SumExt sum → SumHom sum → SumMono sum
  sum-ext+sum-hom⇒sum-mono sum-ext sum-hom {f} {g} f≤°g =
      sum f                         ≤⟨ m≤m+n _ _ ⟩
      sum f + sum (λ x → g x ∸ f x) ≡⟨ ≡.sym (sum-hom _ _) ⟩
      sum (λ x → f x + (g x ∸ f x)) ≡⟨ sum-ext (m+n∸m≡n ∘ f≤°g) ⟩
      sum g ∎ where open ≤-Reasoning

module FromSumInd {a} {A : ★_ a}
                  {sum : Sum A}
                  (sum-ind : SumInd sum) where
  open FromSum sum public

  sum-ext : SumExt sum
  sum-ext = sum-ind (λ s → s _ ≡ s _) ≡.refl (≡.ap₂ _+_)

  sum-zero : SumZero sum
  sum-zero = sum-ind (λ s → s (const 0) ≡ 0) ≡.refl (≡.ap₂ _+_) (λ _ → ≡.refl)

  sum-hom : SumHom sum
  sum-hom f g = sum-ind (λ s → s (f +° g) ≡ s f + s g)
                        ≡.refl
                        (λ {s₀} {s₁} p₀ p₁ → ≡.trans (≡.ap₂ _+_ p₀ p₁) (+-interchange (s₀ _) (s₀ _) _ _))
                        (λ _ → ≡.refl)

  sum-mono : SumMono sum
  sum-mono = sum-ind (λ s → s _ ≤ s _) z≤n _+-mono_

  sum-lin : SumLin sum
  sum-lin f zero    = sum-zero
  sum-lin f (suc k) = ≡.trans (sum-hom f (λ x → k * f x)) (≡.ap₂ _+_ (≡.refl {x = sum f}) (sum-lin f k))

  module _ (f g : A → ℕ) where
    open ≡.≡-Reasoning

    sum-⊓-∸ : sum f ≡ sum (f ⊓° g) + sum (f ∸° g)
    sum-⊓-∸ = sum f                          ≡⟨ sum-ext (f ⟨ a≡a⊓b+a∸b ⟩° g) ⟩
              sum ((f ⊓° g) +° (f ∸° g))     ≡⟨ sum-hom (f ⊓° g) (f ∸° g) ⟩
              sum (f ⊓° g) + sum (f ∸° g) ∎

    sum-⊔-⊓ : sum f + sum g ≡ sum (f ⊔° g) + sum (f ⊓° g)
    sum-⊔-⊓ = sum f + sum g               ≡⟨ ≡.sym (sum-hom f g) ⟩
              sum (f +° g)                ≡⟨ sum-ext (f ⟨ a+b≡a⊔b+a⊓b ⟩° g) ⟩
              sum (f ⊔° g +° f ⊓° g)      ≡⟨ sum-hom (f ⊔° g) (f ⊓° g) ⟩
              sum (f ⊔° g) + sum (f ⊓° g) ∎

    sum-⊔ : sum (f ⊔° g) ≤ sum f + sum g
    sum-⊔ = ℕ≤.trans (sum-mono (f ⟨ ⊔≤+ ⟩° g)) (ℕ≤.reflexive (sum-hom f g))

  count-ext : CountExt count
  count-ext f≗g = sum-ext (≡.cong 𝟚▹ℕ ∘ f≗g)

  sum-const : ∀ k → sum (const k) ≡ Card * k
  sum-const k
      rewrite ℕ°.*-comm Card k
            | ≡.sym (sum-lin (const 1) k)
            | proj₂ ℕ°.*-identity k = ≡.refl

  module _ f g where
    count-∧-not : count f ≡ count (f ∧° g) + count (f ∧° not° g)
    count-∧-not rewrite sum-⊓-∸ (𝟚▹ℕ ∘ f) (𝟚▹ℕ ∘ g)
                      | sum-ext (f ⟨ 𝟚▹ℕ-⊓ ⟩° g)
                      | sum-ext (f ⟨ 𝟚▹ℕ-∸ ⟩° g)
                      = ≡.refl

    count-∨-∧ : count f + count g ≡ count (f ∨° g) + count (f ∧° g)
    count-∨-∧ rewrite sum-⊔-⊓ (𝟚▹ℕ ∘ f) (𝟚▹ℕ ∘ g)
                    | sum-ext (f ⟨ 𝟚▹ℕ-⊔ ⟩° g)
                    | sum-ext (f ⟨ 𝟚▹ℕ-⊓ ⟩° g)
                    = ≡.refl

    count-∨≤+ : count (f ∨° g) ≤ count f + count g
    count-∨≤+ = ℕ≤.trans (ℕ≤.reflexive (sum-ext (≡.sym ∘ (f ⟨ 𝟚▹ℕ-⊔ ⟩° g))))
                         (sum-⊔ (𝟚▹ℕ ∘ f) (𝟚▹ℕ ∘ g))

module FromSum×
         {a} {A : Set a}
         {b} {B : Set b}
         {sumᴬ     : Sum A}
         (sum-indᴬ : SumInd sumᴬ)
         {sumᴮ     : Sum B}
         (sum-indᴮ : SumInd sumᴮ) where

  module |A| = FromSumInd sum-indᴬ
  module |B| = FromSumInd sum-indᴮ
  open Operators

  sumᴬᴮ = sumᴬ ×ˢ sumᴮ

  sum-∘proj₁≡Card* : ∀ f → sumᴬᴮ (f ∘ proj₁) ≡ |B|.Card * sumᴬ f
  sum-∘proj₁≡Card* f
      rewrite |A|.sum-ext (|B|.sum-const ∘ f)
            = |A|.sum-lin f |B|.Card

  sum-∘proj₂≡Card* : ∀ f → sumᴬᴮ (f ∘ proj₂) ≡ |A|.Card * sumᴮ f
  sum-∘proj₂≡Card* = |A|.sum-const ∘ sumᴮ

  sum-∘proj₁ : ∀ {f} {g} → sumᴬ f ≡ sumᴬ g → sumᴬᴮ (f ∘ proj₁) ≡ sumᴬᴮ (g ∘ proj₁)
  sum-∘proj₁ {f} {g} sumf≡sumg
      rewrite sum-∘proj₁≡Card* f
            | sum-∘proj₁≡Card* g
            | sumf≡sumg = ≡.refl

  sum-∘proj₂ : ∀ {f} {g} → sumᴮ f ≡ sumᴮ g → sumᴬᴮ (f ∘ proj₂) ≡ sumᴬᴮ (g ∘ proj₂)
  sum-∘proj₂ sumf≡sumg = |A|.sum-ext (const sumf≡sumg)

-- -}
-- -}
-- -}
-- -}
