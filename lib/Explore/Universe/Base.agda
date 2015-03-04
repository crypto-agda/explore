{-# OPTIONS --without-K #-}
open import Level.NP
open import Type
open import Type.Identities
open import Function.NP
open import Function.Extensionality
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Product.NP
open import Data.Sum.NP
open import Data.Sum.Logical
open import Data.Nat
open import Data.Fin
open import Relation.Nullary.NP
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Binary.Logical

open import HoTT
open Equivalences

open import Explore.Core
open import Explore.Properties
open import Explore.Zero
open import Explore.One
open import Explore.Two
open import Explore.Product
open import Explore.Sum
open import Explore.Explorable
open import Explore.Universe
import Explore.Isomorphism

module Explore.Universe.Base where

module _ {k} {K : ★_ k} {a} {A : ★_ a} {x y : A} (p : x ≡ y) where
    tr-const : tr (const K) p ≡ id
    tr-const = J (λ x₁ p₁ → tr (const K) p₁ ≡ id) refl p

open FromKit 𝟘ⁱ (λ {{ua}}{{_}} → 𝟘ˢ-ok {{ua}}) 𝟘ˡ 𝟘ᶠ
             (λ {{ua}} → Σᵉ𝟘-ok {{ua}})
             Πᵉ𝟘-ok (λ {ℓ₀ ℓ₁} ℓᵣ → ⟦𝟘ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} {_≡_}) public

Πᵁ : (u : U) (v : El u → U) → U
Πᵁ 𝟘ᵁ        v = 𝟙ᵁ
Πᵁ 𝟙ᵁ        v = v _
Πᵁ 𝟚ᵁ        v = v 0₂ ×ᵁ v 1₂
Πᵁ (u ×ᵁ u₁) v = Πᵁ u λ x → Πᵁ u₁ λ y → v (x , y)
Πᵁ (u ⊎ᵁ u₁) v = (Πᵁ u (v ∘ inl)) ×ᵁ (Πᵁ u₁ (v ∘ inr))
Πᵁ (Σᵁ u f)  v = Πᵁ u λ x → Πᵁ (f x) (v ∘ _,_ x)
Πᵁ Xᵁ        v = 𝟙ᵁ

_→ᵁ_ : (u : U) (v : U) → U
u →ᵁ v = Πᵁ u (const v)

module _ {{_ : FunExt}}{{_ : UA}} where
  Πᵁ-Π : ∀ u v → El (Πᵁ u v) ≡ Π (El u) (El ∘ v)
  Πᵁ-Π 𝟘ᵁ        v = ! Π𝟘-uniq₀ _
  Πᵁ-Π 𝟙ᵁ        v = ! Π𝟙-uniq _
  Πᵁ-Π 𝟚ᵁ        v = ! Π𝟚-×
  Πᵁ-Π (u ×ᵁ u₁) v = Πᵁ-Π u (λ x → Πᵁ u₁ (v ∘ _,_ x)) ∙ Π=′ _ (λ _ → Πᵁ-Π u₁ _) ∙ ! ΠΣ-curry
  Πᵁ-Π (u ⊎ᵁ u₁) v = ×= (Πᵁ-Π u (v ∘ inl)) (Πᵁ-Π u₁ (v ∘ inr)) ∙ ! dist-×-Π
  Πᵁ-Π (Σᵁ u f)  v = Πᵁ-Π u (λ x → Πᵁ (f _) (v ∘ _,_ x)) ∙ Π=′ _ (λ _ → Πᵁ-Π (f _) _) ∙ ! ΠΣ-curry
  Πᵁ-Π Xᵁ        v = ! Π𝟘-uniq₀ _

  →ᵁ-→ : ∀ u v → El (u →ᵁ v) ≡ (El u → El v)
  →ᵁ-→ u v = Πᵁ-Π u (const v)

Πᵁ→Π : ∀ u v → El (Πᵁ u v) → Π (El u) (El ∘ v)
Πᵁ→Π 𝟘ᵁ v x₂ ()
Πᵁ→Π 𝟙ᵁ v x₂ x₃ = x₂
Πᵁ→Π 𝟚ᵁ v (x , y) 0₂ = x
Πᵁ→Π 𝟚ᵁ v (x , y) 1₂ = y
Πᵁ→Π (u ×ᵁ u₁) v x (z , t) = Πᵁ→Π u₁ (v ∘ _,_ z) (Πᵁ→Π u (λ x → Πᵁ u₁ (v ∘ _,_ x)) x z) t
Πᵁ→Π (u ⊎ᵁ _) v (x , _) (inl y) = Πᵁ→Π u (v ∘ inl) x y
Πᵁ→Π (_ ⊎ᵁ u) v (_ , x) (inr y) = Πᵁ→Π u (v ∘ inr) x y
Πᵁ→Π (Σᵁ u f) v x       (y , z) = Πᵁ→Π (f _) (v ∘ _,_ y) (Πᵁ→Π u (λ x → Πᵁ (f _) (v ∘ _,_ x)) x y) z
Πᵁ→Π Xᵁ v x₂ ()

Π→Πᵁ : ∀ u v → Π (El u) (El ∘ v) → El (Πᵁ u v)
Π→Πᵁ 𝟘ᵁ v f = 0₁
Π→Πᵁ 𝟙ᵁ v f = f 0₁
Π→Πᵁ 𝟚ᵁ v f = f 0₂ , f 1₂
Π→Πᵁ (u ×ᵁ u₁) v f = Π→Πᵁ u (λ x → Πᵁ u₁ (v ∘ _,_ x))
                       (λ x → Π→Πᵁ u₁ (v ∘ _,_ x) (f ∘ _,_ x))
Π→Πᵁ (u ⊎ᵁ u₁) v f = Π→Πᵁ u (v ∘ inl) (f ∘ inl) ,
                       Π→Πᵁ u₁ (v ∘ inr) (f ∘ inr)
Π→Πᵁ (Σᵁ u F) v f = Π→Πᵁ u (λ x → Πᵁ (F x) (v ∘ _,_ x))
                      (λ x → Π→Πᵁ (F x) (v ∘ _,_ x) (f ∘ _,_ x))
Π→Πᵁ Xᵁ v f = 0₁

→ᵁ→→ : ∀ u v → El (u →ᵁ v) → (El u → El v)
→ᵁ→→ u v = Πᵁ→Π u (const v)

→→→ᵁ : ∀ u v → (El u → El v) → El (u →ᵁ v)
→→→ᵁ u v = Π→Πᵁ u (const v)

{-
⟦U⟧-sound : ∀ {{_ : FunExt}} {x y} → ⟦U⟧ x y → x ≡ y
⟦U⟧-refl : ∀ x → ⟦U⟧ x x

{-
⟦El⟧-refl : ∀ x → {!⟦El⟧ x x!}
⟦El⟧-refl = {!!}
-}

⟦U⟧-sound ⟦𝟘ᵁ⟧ = refl
⟦U⟧-sound ⟦𝟙ᵁ⟧ = refl
⟦U⟧-sound ⟦𝟚ᵁ⟧ = refl
⟦U⟧-sound (u ⟦×ᵁ⟧ u₁) = ap₂ _×ᵁ_ (⟦U⟧-sound u) (⟦U⟧-sound u₁)
⟦U⟧-sound (u ⟦⊎ᵁ⟧ u₁) = ap₂ _⊎ᵁ_ (⟦U⟧-sound u) (⟦U⟧-sound u₁)
⟦U⟧-sound (⟦Σᵁ⟧ {u₀} {u₁} u {f₀} {f₁} fᵣ) = apd₂ Σᵁ (⟦U⟧-sound u) (tr-→ El (const U) (⟦U⟧-sound u) f₀ ∙ λ= (λ A → ap (λ z → z (f₀ (tr El (! ⟦U⟧-sound u) A))) (tr-const (⟦U⟧-sound u)) ∙ ⟦U⟧-sound (fᵣ {!!}))) -- (λ= (λ y → let foo = xᵣ {{!!}} {y} {!xᵣ!} in {!tr-→ El (const U) (⟦U⟧-sound u)!}))

⟦U⟧-refl 𝟘ᵁ = ⟦𝟘ᵁ⟧
⟦U⟧-refl 𝟙ᵁ = ⟦𝟙ᵁ⟧
⟦U⟧-refl 𝟚ᵁ = ⟦𝟚ᵁ⟧
⟦U⟧-refl (x ×ᵁ x₁) = ⟦U⟧-refl x ⟦×ᵁ⟧ ⟦U⟧-refl x₁
⟦U⟧-refl (x ⊎ᵁ x₁) = ⟦U⟧-refl x ⟦⊎ᵁ⟧ ⟦U⟧-refl x₁
⟦U⟧-refl (Σᵁ x f) = ⟦Σᵁ⟧ (⟦U⟧-refl x) (λ y → {!⟦U⟧-refl ?!})
-}

-- -}
-- -}
-- -}
-- -}
-- -}
