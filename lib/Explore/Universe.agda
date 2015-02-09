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
import Explore.Isomorphism

module Explore.Universe where

open Operators

infixr 2 _×ᵁ_

data U : ★
El : U → ★

data U where
  𝟘ᵁ 𝟙ᵁ 𝟚ᵁ : U
  _×ᵁ_ _⊎ᵁ_ : U → U → U
  Σᵁ : (t : U) (f : El t → U) → U

El 𝟘ᵁ = 𝟘
El 𝟙ᵁ = 𝟙
El 𝟚ᵁ = 𝟚
El (s ×ᵁ t) = El s × El t
El (s ⊎ᵁ t) = El s ⊎ El t
El (Σᵁ t f) = Σ (El t) λ x → El (f x)

data ⟦U⟧ : ⟦★₀⟧ U U
⟦El⟧ : (⟦U⟧ ⟦→⟧ ⟦★₀⟧) El El

data ⟦U⟧ where
  ⟦𝟘ᵁ⟧ : ⟦U⟧ 𝟘ᵁ 𝟘ᵁ
  ⟦𝟙ᵁ⟧ : ⟦U⟧ 𝟙ᵁ 𝟙ᵁ
  ⟦𝟚ᵁ⟧ : ⟦U⟧ 𝟚ᵁ 𝟚ᵁ
  _⟦×ᵁ⟧_ : ⟦Op₂⟧ ⟦U⟧ _×ᵁ_ _×ᵁ_
  _⟦⊎ᵁ⟧_ : ⟦Op₂⟧ ⟦U⟧ _⊎ᵁ_ _⊎ᵁ_
  ⟦Σᵁ⟧ : (⟨ t ∶ ⟦U⟧ ⟩⟦→⟧ (⟦El⟧ t ⟦→⟧ ⟦U⟧) ⟦→⟧ ⟦U⟧) Σᵁ Σᵁ

⟦El⟧ ⟦𝟘ᵁ⟧ = _≡_
⟦El⟧ ⟦𝟙ᵁ⟧ = _≡_
⟦El⟧ ⟦𝟚ᵁ⟧ = _≡_
⟦El⟧ (s ⟦×ᵁ⟧ t) = ⟦El⟧ s ⟦×⟧ ⟦El⟧ t
⟦El⟧ (s ⟦⊎ᵁ⟧ t) = ⟦El⟧ s ⟦⊎⟧ ⟦El⟧ t
⟦El⟧ (⟦Σᵁ⟧ t f) = ⟦Σ⟧ (⟦El⟧ t) λ x → ⟦El⟧ (f x)

module _ {k} {K : ★_ k} {a} {A : ★_ a} {x y : A} (p : x ≡ y) where
    tr-const : tr (const K) p ≡ id
    tr-const = J (λ x₁ p₁ → tr (const K) p₁ ≡ id) refl p

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

infix  8 _^ᵁ_
_^ᵁ_ : U → ℕ → U
t ^ᵁ zero  = t
t ^ᵁ suc n = t ×ᵁ t ^ᵁ n

module _ {ℓ} where

    explore : ∀ t → Explore ℓ (El t)
    explore 𝟘ᵁ = 𝟘ᵉ
    explore 𝟙ᵁ = 𝟙ᵉ
    explore 𝟚ᵁ = 𝟚ᵉ
    explore (s ×ᵁ t) = explore s ×ᵉ explore t
    explore (s ⊎ᵁ t) = explore s ⊎ᵉ explore t
    explore (Σᵁ t f) = exploreΣ (explore t) λ {x} → explore (f x)

    exploreU-ind : ∀ {p} t → ExploreInd p (explore t)
    exploreU-ind 𝟘ᵁ = 𝟘ⁱ
    exploreU-ind 𝟙ᵁ = 𝟙ⁱ
    exploreU-ind 𝟚ᵁ = 𝟚ⁱ
    exploreU-ind (s ×ᵁ t) = exploreU-ind s ×ⁱ exploreU-ind t
    exploreU-ind (s ⊎ᵁ t) = exploreU-ind s ⊎ⁱ exploreU-ind t
    exploreU-ind (Σᵁ t f) = exploreΣ-ind (exploreU-ind t) λ {x} → exploreU-ind (f x)

module _ {ℓ₀ ℓ₁ ℓᵣ} where
    ⟦explore⟧ : ∀ {t₀ t₁} (t : ⟦U⟧ t₀ t₁) → ⟦Explore⟧ {ℓ₀} {ℓ₁} ℓᵣ (⟦El⟧ t) (explore t₀) (explore t₁)
    ⟦explore⟧ ⟦𝟘ᵁ⟧        = ⟦𝟘ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ}
    ⟦explore⟧ ⟦𝟙ᵁ⟧        = ⟦𝟙ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} {_≡_} {refl}
    ⟦explore⟧ ⟦𝟚ᵁ⟧        = ⟦𝟚ᵉ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} {_≡_} {refl} {refl}
    ⟦explore⟧ (t ⟦×ᵁ⟧ t₁) = ⟦explore×⟧ {ℓ₀} {ℓ₁} {ℓᵣ} (⟦explore⟧ t) (⟦explore⟧ t₁)
    ⟦explore⟧ (t ⟦⊎ᵁ⟧ t₁) = ⟦explore⊎⟧ {ℓ₀} {ℓ₁} {ℓᵣ} (⟦explore⟧ t) (⟦explore⟧ t₁)
    ⟦explore⟧ (⟦Σᵁ⟧ t f)  = ⟦exploreΣ⟧ {ℓ₀} {ℓ₁} {ℓᵣ} (⟦explore⟧ t) (⟦explore⟧ ∘ f)

module _ (t : U) where
  private
    tᵉ : ∀ {ℓ} → Explore ℓ (El t)
    tᵉ = explore t
    tⁱ : ∀ {ℓ p} → ExploreInd {ℓ} p tᵉ
    tⁱ = exploreU-ind t

  open FromExploreInd tⁱ public hiding (⟦explore⟧)
  {-
  open From⟦Explore⟧ (λ {ℓ₁} {ℓ₂} {ℓᵣ} → ⟦explore⟧' {ℓ₁} {ℓ₂} {ℓᵣ} t) public
  -}

adequate-sumU : ∀ {{_ : UA}}{{_ : FunExt}} t → Adequate-sum (sum t)
adequate-sumU 𝟘ᵁ       = 𝟘ˢ-ok
adequate-sumU 𝟙ᵁ       = 𝟙ˢ-ok
adequate-sumU 𝟚ᵁ       = 𝟚ˢ-ok
adequate-sumU (s ×ᵁ t) = adequate-sumΣ (adequate-sumU s) (adequate-sumU t)
adequate-sumU (s ⊎ᵁ t) = adequate-sum⊎ (adequate-sumU s) (adequate-sumU t)
adequate-sumU (Σᵁ t f) = adequate-sumΣ (adequate-sumU t) (λ {x} → adequate-sumU (f x))

module _ {ℓ} where
    lookupU : ∀ t → Lookup {ℓ} (explore t)
    lookupU 𝟘ᵁ = 𝟘ˡ
    lookupU 𝟙ᵁ = 𝟙ˡ
    lookupU 𝟚ᵁ = 𝟚ˡ
    lookupU (s ×ᵁ t) = lookup× {eᴬ = explore s} {eᴮ = explore t} (lookupU s) (lookupU t)
    lookupU (s ⊎ᵁ t) = lookup⊎ {eᴬ = explore s} {eᴮ = explore t} (lookupU s) (lookupU t)
    lookupU (Σᵁ t f) = lookupΣ {eᴬ = explore t} {eᴮ = λ {x} → explore (f x)} (lookupU t) (λ {x} → lookupU (f x))

    focusU : ∀ t → Focus {ℓ} (explore t)
    focusU 𝟘ᵁ = 𝟘ᶠ
    focusU 𝟙ᵁ = 𝟙ᶠ
    focusU 𝟚ᵁ = 𝟚ᶠ
    focusU (s ×ᵁ t) = focus× {eᴬ = explore s} {eᴮ = explore t} (focusU s) (focusU t)
    focusU (s ⊎ᵁ t) = focus⊎ {eᴬ = explore s} {eᴮ = explore t} (focusU s) (focusU t)
    focusU (Σᵁ t f) = focusΣ {eᴬ = explore t} {eᴮ = λ {x} → explore (f x)} (focusU t) (λ {x} → focusU (f x))

    ΣᵉU : ∀ A {ℓ} → (El A → ★_ ℓ) → ★_ ℓ
    ΣᵉU = λ A → Σᵉ (explore A)
    ΠᵉU : ∀ A {ℓ} → (El A → ★_ ℓ) → ★_ ℓ
    ΠᵉU = λ A → Πᵉ (explore A)

    module _ {{_ : UA}}{{_ : FunExt}} where
        ΣᵉU-ok : ∀ t → Adequate-Σ {ℓ} (ΣᵉU t)
        ΣᵉU-ok 𝟘ᵁ       = Σᵉ𝟘-ok
        ΣᵉU-ok 𝟙ᵁ       = Σᵉ𝟙-ok
        ΣᵉU-ok 𝟚ᵁ       = Σᵉ𝟚-ok
        ΣᵉU-ok (t ×ᵁ u) = Σᵉ×-ok {eᴬ = explore t} {eᴮ = explore u} (ΣᵉU-ok t) (ΣᵉU-ok u)
        ΣᵉU-ok (t ⊎ᵁ u) = Σᵉ⊎-ok {eᴬ = explore t} {eᴮ = explore u} (ΣᵉU-ok t) (ΣᵉU-ok u)
        ΣᵉU-ok (Σᵁ t u) = ΣᵉΣ-ok {eᴬ = explore t} {eᴮ = λ {x} → explore (u x)} (ΣᵉU-ok t) (λ {x} → ΣᵉU-ok (u x))

        ΠᵉU-ok : ∀ t → Adequate-Π {ℓ} (ΠᵉU t)
        ΠᵉU-ok 𝟘ᵁ       = Πᵉ𝟘-ok
        ΠᵉU-ok 𝟙ᵁ       = Πᵉ𝟙-ok
        ΠᵉU-ok 𝟚ᵁ       = Πᵉ𝟚-ok
        ΠᵉU-ok (t ×ᵁ u) = Πᵉ×-ok {eᴬ = explore t} {eᴮ = explore u} (ΠᵉU-ok t) (ΠᵉU-ok u)
        ΠᵉU-ok (t ⊎ᵁ u) = Πᵉ⊎-ok {eᴬ = explore t} {eᴮ = explore u} (ΠᵉU-ok t) (ΠᵉU-ok u)
        ΠᵉU-ok (Σᵁ t u) = ΠᵉΣ-ok {eᴬ = explore t} {eᴮ = λ {x} → explore (u x)} (ΠᵉU-ok t) (λ {x} → ΠᵉU-ok (u x))

{-
module _ (t : U) {{_ : UA}} {{_ : FunExt}} where
  open FromAdequate-Σᵉ t (ΣᵉU-ok t) public
  open FromAdequate-Πᵉ t (ΠᵉU-ok t) public
-}

module _ (A : U) (P : El A → ★₀) where
    Dec-Σ : Π (El A) (Dec ∘ P) → Dec (Σ (El A) P)
    Dec-Σ = map-Dec (unfocus A) (focusU A) ∘ lift-Dec A P ∘ reify A

-- See Explore.Fin for an example of the use of this module
module Isomorphism {A : ★₀} u (e : El u ≃ A) where
  open Explore.Isomorphism e

  module _ {ℓ} where
    isoᵉ : Explore ℓ A
    isoᵉ = explore-iso (explore u)

    module _ {p} where
      isoⁱ : ExploreInd p isoᵉ
      isoⁱ = explore-iso-ind (exploreU-ind u)

  module _ {ℓ} where
  {-
    isoˡ : Lookup {ℓ} isoᵉ
    isoˡ = lookup-iso {ℓ} {exploreU u} (lookupU u)

    isoᶠ : Focus {ℓ} isoᵉ
    isoᶠ = focus-iso {ℓ} {exploreU u} (focusU u)
    -}

    isoʳ : Reify {ℓ} isoᵉ
    isoʳ = FromExploreInd-iso.reify (exploreU-ind u)

    isoᵘ : Unfocus {ℓ} isoᵉ
    isoᵘ = FromExploreInd-iso.unfocus (exploreU-ind u)

  isoˢ : Sum A
  isoˢ = sum-iso (sum u)

  isoᵖ : Product A
  isoᵖ = product-iso (sum u)

  module _ {{_ : UA}}{{_ : FunExt}} where
    isoˢ-ok : Adequate-sum isoˢ
    isoˢ-ok = sum-iso-ok (adequate-sumU u)

    open Adequate-sum₀ isoˢ-ok isoˢ-ok public renaming (sumStableUnder to isoˢ-stableUnder)

Finᵁ : ℕ → U
Finᵁ zero    = 𝟘ᵁ
Finᵁ (suc n) = 𝟙ᵁ ⊎ᵁ Finᵁ n

Finᵁ' : ℕ → U
Finᵁ' zero          = 𝟘ᵁ
Finᵁ' (suc zero)    = 𝟙ᵁ
Finᵁ' (suc (suc n)) = 𝟙ᵁ ⊎ᵁ Finᵁ' (suc n)

Finᵁ-Fin : ∀ n → El (Finᵁ n) ≃ Fin n
Finᵁ-Fin zero    = ≃-! Fin0≃𝟘
Finᵁ-Fin (suc n) = ⊎≃ ≃-refl (Finᵁ-Fin n) ≃-∙ ≃-! Fin∘suc≃𝟙⊎Fin

Finᵁ'-Fin : ∀ n → El (Finᵁ' n) ≃ Fin n
Finᵁ'-Fin zero          = ≃-! Fin0≃𝟘
Finᵁ'-Fin (suc zero)    = ≃-! Fin1≃𝟙
Finᵁ'-Fin (suc (suc n)) = ⊎≃ ≃-refl (Finᵁ'-Fin (suc n)) ≃-∙ ≃-! Fin∘suc≃𝟙⊎Fin

Πᵁ : (u : U) (v : El u → U) → U
Πᵁ 𝟘ᵁ        v = 𝟙ᵁ
Πᵁ 𝟙ᵁ        v = v _
Πᵁ 𝟚ᵁ        v = v 0₂ ×ᵁ v 1₂
Πᵁ (u ×ᵁ u₁) v = Πᵁ u λ x → Πᵁ u₁ λ y → v (x , y)
Πᵁ (u ⊎ᵁ u₁) v = (Πᵁ u (v ∘ inl)) ×ᵁ (Πᵁ u₁ (v ∘ inr))
Πᵁ (Σᵁ u f)  v = Πᵁ u λ x → Πᵁ (f x) (v ∘ _,_ x)

_→ᵁ_ : (u : U) (v : U) → U
u →ᵁ v = Πᵁ u (const v)

{-
𝟛ᵁ : U
𝟛ᵁ = 𝟙ᵁ ⊎ᵁ 𝟚ᵁ

list22 = list (𝟚ᵁ →ᵁ 𝟚ᵁ)
list33 = list (𝟛ᵁ →ᵁ 𝟛ᵁ)
-}

module _ {{_ : UA}}{{_ : FunExt}} where
    Πᵁ-Π : ∀ u v → El (Πᵁ u v) ≡ Π (El u) (El ∘ v)
    Πᵁ-Π 𝟘ᵁ        v = ! Π𝟘-uniq₀ _
    Πᵁ-Π 𝟙ᵁ        v = ! Π𝟙-uniq _
    Πᵁ-Π 𝟚ᵁ        v = ! Π𝟚-×
    Πᵁ-Π (u ×ᵁ u₁) v = Πᵁ-Π u (λ x → Πᵁ u₁ (v ∘ _,_ x)) ∙ Π=′ _ (λ _ → Πᵁ-Π u₁ _) ∙ ! ΠΣ-curry
    Πᵁ-Π (u ⊎ᵁ u₁) v = ×= (Πᵁ-Π u (v ∘ inl)) (Πᵁ-Π u₁ (v ∘ inr)) ∙ ! dist-×-Π
    Πᵁ-Π (Σᵁ u f)  v = Πᵁ-Π u (λ x → Πᵁ (f _) (v ∘ _,_ x)) ∙ Π=′ _ (λ _ → Πᵁ-Π (f _) _) ∙ ! ΠΣ-curry

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

    →ᵁ→→ : ∀ u v → El (u →ᵁ v) → (El u → El v)
    →ᵁ→→ u v = Πᵁ→Π u (const v)

-- -}
-- -}
-- -}
-- -}
-- -}
