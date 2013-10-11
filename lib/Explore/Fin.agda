{-# OPTIONS --without-K #-}

open import Level.NP
open import Type
open import Function
open import Algebra
open import Algebra.FunctionProperties.NP
open import Data.Fin using (Fin; zero; suc)
open import Data.Zero
open import Data.One
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as Inv
open Inv using (_↔_; sym; id; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Relation.Binary.NP
open import Explore.Type
open import Explore.Explorable
import Explore.Isomorphism as Iso
--open import Explore.Explorable.Maybe

module Explore.Fin where

𝟙⊎^ : ℕ → ★₀
𝟙⊎^ zero    = 𝟘
𝟙⊎^ (suc n) = 𝟙 ⊎ 𝟙⊎^ n

Fin↔𝟙⊎^𝟘 : ∀ n → Fin n ↔ 𝟙⊎^ n
Fin↔𝟙⊎^𝟘 zero    = Fin0↔𝟘
Fin↔𝟙⊎^𝟘 (suc n) = {!{!Inv.id!} ⊎-cong ?!} Inv.∘ Fin∘suc↔𝟙⊎Fin

{-
Maybe^𝟘↔Fin
open Iso (Fin

{-
module _ {ℓ} where
    Finᵉ : ∀ n → Explore ℓ (Fin n)
    Finᵉ zero    z _∙_ f = z
    Finᵉ (suc n) z _∙_ f = f zero ∙ Finᵉ n z _∙_ (f ∘ suc)

    Finⁱ : ∀ {p} n → ExploreInd p (Finᵉ n)
    Finⁱ zero    P z _∙_ f = z
    Finⁱ (suc n) P z _∙_ f = f zero ∙ Finⁱ n Psuc z _∙_ (f ∘ suc)
      where Psuc = λ e → P (λ z op f → e z op (f ∘ suc))

module _ {ℓ} where
    Finˡ : ∀ n → Lookup {ℓ} (Finᵉ n)
    Finˡ (suc _) (b , _)  zero    = b
    Finˡ (suc n) (_ , xs) (suc x) = Finˡ n xs x

    Finᶠ : ∀ n → Focus {ℓ} (Finᵉ n)
    Finᶠ (suc n) (zero   , b) = inj₁ b
    Finᶠ (suc n) (suc x  , b) = inj₂ (Finᶠ n (x , b))

module _ n where
    open Explorable₀  (Finⁱ n) public using () renaming (sum     to Finˢ; product to Finᵖ)
    open Explorable₁₀ (Finⁱ n) public using () renaming (reify   to Finʳ)
    open Explorable₁₁ (Finⁱ n) public using () renaming (unfocus to Finᵘ)

postulate
  Postulate-Finˢ-ok : ★
  Postulate-FinFunˢ-ok : ★

  Finˢ-ok : ∀ {{_ : Postulate-Finˢ-ok}} n → AdequateSum (Finˢ n)

{-
Finᵖ-ok : ∀ n → AdequateProduct (Finᵖ n)
-}

module _ {A : ★}(μA : Explorable A) where

  eᴬ = explore μA

  extend : ∀ {n} → A → (Fin n → A) → Fin (suc n) → A
  extend x g zero    = x
  extend x g (suc i) = g i

  ¬Fin0 : Fin 0 → A
  ¬Fin0 ()

  -- There is one function Fin 0 → A (called abs) so this should be fine
  -- if not there is a version below that forces the domain to be non-empty
  FinFunᵉ : ∀ n → Explore _ (Fin n → A)
  FinFunᵉ zero    z op f = f ¬Fin0
  FinFunᵉ (suc n) z op f = eᴬ z op (λ x → FinFunᵉ n z op (f ∘ extend x))

  FinFunⁱ : ∀ n → ExploreInd _ (FinFunᵉ n)
  FinFunⁱ zero    P Pz P∙ Pf = Pf _
  FinFunⁱ (suc n) P Pz P∙ Pf =
    explore-ind μA (λ sa → P (λ z op f → sa z op (λ x → FinFunᵉ n z op (f ∘ extend x))))
      Pz P∙
      (λ x → FinFunⁱ n (λ sf → P (λ z op f → sf z op (f ∘ extend x)))
        Pz P∙ (Pf ∘ extend x))

  FinFunˢ : ∀ n → Sum (Fin n → A)
  FinFunˢ n = FinFunᵉ n 0 _+_

  postulate
    FinFunˢ-ok : ∀ {{_ : Postulate-FinFunˢ-ok}} n → AdequateSum (FinFunˢ n)

  μFinFun : ∀ {{_ : Postulate-FinFunˢ-ok}} {n} → Explorable (Fin n → A)
  μFinFun = mk _ (FinFunⁱ _) (FinFunˢ-ok _)

μFin : ∀ {{_ : Postulate-Finˢ-ok}} n → Explorable (Fin n)
μFin n = mk _ (Finⁱ n) (Finˢ-ok n)

{-
μFinSUI : ∀ {n} → SumStableUnderInjection (sum (μFin n))
-}

module BigDistr
  {{_ : Postulate-Finˢ-ok}}
  {{_ : Postulate-FinFunˢ-ok}}
  {A : ★}(μA : Explorable A)
  (cm           : CommutativeMonoid ₀ ₀)
  -- we want (open CMon cm) !!!
  (_◎_          : let open CMon cm in C → C → C)
  (ε-◎          : let open CMon cm in Zero _≈_ ε _◎_)
  (distrib      : let open CMon cm in _DistributesOver_ _≈_ _◎_ _∙_)
  (_◎-cong_     : let open CMon cm in _◎_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_) where

  open CMon cm renaming (sym to ≈-sym)

  μF→A = μFinFun μA

  -- Sum over A
  Σᴬ = explore μA ε _∙_

  -- Sum over (Fin(1+I)→A) functions
  Σ' : ∀ {I} → ((Fin I → A) → C) → C
  Σ' = explore μF→A ε _∙_

  -- Product over Fin(1+I) values
  Π' = λ I → explore (μFin I) ε _◎_

  bigDistr : ∀ I F → Π' I (Σᴬ ∘ F) ≈ Σ' (Π' I ∘ _ˢ_ F)
  bigDistr zero    _ = refl
  bigDistr (suc I) F
    = Σᴬ (F zero) ◎ Π' I (Σᴬ ∘ F ∘ suc)
    ≈⟨ refl ◎-cong bigDistr I (F ∘ suc) ⟩
      Σᴬ (F zero) ◎ Σ' (Π' I ∘ _ˢ_ (F ∘ suc))
    ≈⟨ ≈-sym (explore-linʳ μA monoid _◎_ (F zero) (Σ' (Π' I ∘ _ˢ_ (F ∘ suc))) (proj₁ ε-◎ _) (proj₂ distrib)) ⟩
      Σᴬ (λ j → F zero j ◎ Σ' (Π' I ∘ _ˢ_ (F ∘ suc)))
    ≈⟨ explore-mon-ext μA monoid (λ j → ≈-sym (explore-linˡ μF→A monoid _◎_ (Π' I ∘ _ˢ_ (F ∘ suc)) (F zero j) (proj₂ ε-◎ _) (proj₁ distrib))) ⟩
      (Σᴬ λ j → Σ' λ f → F zero j ◎ Π' I ((F ∘ suc) ˢ f))
    ∎

module _
  {{_ : Postulate-Finˢ-ok}}
  {{_ : Postulate-FinFunˢ-ok}} where

  FinDist : ∀ {n} → DistFun (μFin n) (λ μX → μFinFun μX)
  FinDist μB c ◎ distrib ◎-cong f = BigDistr.bigDistr μB c ◎ distrib ◎-cong f _
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
