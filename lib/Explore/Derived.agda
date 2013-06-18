module Explore.Derived where

open import Function
open import Data.Nat.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_)
open import Data.Nat.Properties
open import Explore.Type
open import Explore.Explorable

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
