{-# OPTIONS --without-K #-}
module factorial where

open import Type
open import Data.Nat.NP
open import Data.Product
open import Data.Sum.NP
open import Data.Zero
open import Data.Maybe
open import Data.One using (𝟙)
open import Data.Fin.NP using (Fin; Fin′; zero; suc;
                               inject₁; inject!;
                               Fin▹ℕ; ℕ▹Fin; [zero:_,suc:_])
open import Function.NP
open import Function.Extensionality
open import HoTT
open Equivalences
open import Type.Identities
open import Algebra.FunctionProperties.Eq
{-
open import Function.Related as FR
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as I
open I using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.Sum
-}
open import Relation.Binary.PropositionalEquality.NP
  renaming (!_ to ¡_)
open ≡-Reasoning

-- n ! ≡ product [1..n]

module v1 where
  _! : ℕ → ℕ
  zero  ! = 1
  suc n ! = (1 + n) * n !

  _!★ : ℕ → ★
  zero  !★ = 𝟙
  suc n !★ = Fin (1 + n) × n !★

  module _ {{_ : UA}} where
    !★≡Fin! : ∀ {n} → n !★ ≡ Fin (n !)
    !★≡Fin! {zero}  = ¡ Fin1≡𝟙
    !★≡Fin! {suc n} = ×= idp !★≡Fin! ∙ Fin-×-*

module v2 where
  _! : ℕ → ℕ
  _+1! : ℕ → ℕ

  zero  ! = 1
  suc n ! = n +1!

  n +1! = n ! + n * n !

  _!★ : ℕ → ★
  zero  !★ = 𝟙
  suc n !★ = n !★ ⊎ Fin n × n !★

  1+_!★ : ℕ → ★
  1+ n !★ = n !★ ⊎ Fin n × n !★

  module _ {{_ : UA}} where
    !★≡Fin! : ∀ {n} → n !★ ≡ Fin (n !)
    !★≡Fin! {zero}  = ¡ Fin1≡𝟙
    !★≡Fin! {suc n} = ⊎= !★≡Fin! (×= idp !★≡Fin! ∙ Fin-×-*)
                    ∙ Fin-⊎-+

productFin : ∀ n → (Fin n → ℕ) → ℕ
productFin zero    f = 1
productFin (suc n) f = f zero * productFin n (f ∘ suc)

product[0…_] : ℕ → (ℕ → ℕ) → ℕ
product[0… n ] f = productFin n (f ∘ Fin▹ℕ)
{-
product[0… zero  ] f = 1
product[0… suc n ] f = f zero * product[0… n ] (f ∘ suc)
-}

product[1…_] : ℕ → (ℕ → ℕ) → ℕ
product[1… zero  ] f = 1
product[1… suc n ] f = f 1 * product[1… n ] (f ∘ suc)

product[_to_] : ℕ → ℕ → (ℕ → ℕ) → ℕ
product[ start to stop ] f = product[0… stop ∸ start ] (f ∘ _+_ start)

{-
data Bnd (l : ℕ) : (h : ℕ) → Set where
  low : Bnd l (suc l)
  suc : ∀ {h} → Bnd l h → Bnd l (suc h)

Bnd▹ℕ : {l h : ℕ} → Bnd l h → ℕ
Bnd▹ℕ {l} low = l
Bnd▹ℕ (suc x) = suc (Bnd▹ℕ x)

productBnd : ∀ {l h} → l ≤ h → (Bnd l h → ℕ) → ℕ
productBnd z≤n f = {!!}
productBnd (s≤s p) f = {!!}

productBnd p f = {!f low * productBnd l h (f ∘ suc)!}
-}

test-product[1…3] : product[1… 3 ] ≡ (λ f → f 1 * (f 2 * (f 3 * 1)))
test-product[1…3] = idp

open v1
{-
adequate1 : ∀ n → n ! ≡ product[1… n ] id
adequate1 zero = ≡.refl
adequate1 (suc n) rewrite adequate1 n = {!!}
  Π{x∈1…n}x + n * Π{x∈1…n}x

  (1 + n) * Π{x∈1…n}x

  Π{x∈1…n}1+x
  -}


Π[0…_-1] : ℕ → (ℕ → ℕ) → ★
Π[0… n -1] f = Π (Fin n) (Fin ∘ f ∘ Fin▹ℕ)

Π[0…_] : ℕ → (ℕ → ℕ) → ★
Π[0… n ] = Π[0… suc n -1]

{-
Π[1…_] : ℕ → (ℕ → ℕ) → ★
Π[1… 0     ] f = 𝟙
Π[1… suc n ] f = {!!}
-}

Π[0…_-1]′ : ℕ → (ℕ → ℕ) → ★
Π[0… zero  -1]′ f = 𝟙
Π[0… suc n -1]′ f = Fin (f 0) × Π[0… n -1]′ (f ∘ suc)

Π[0…_]′ : ℕ → (ℕ → ℕ) → ★
Π[0… n ]′ = Π[0… suc n -1]′

{-
Π[1…_]′ : ℕ → (ℕ → ℕ) → ★
Π[1… zero  ]′ f = 𝟙
Π[1… suc n ]′ f = Fin (f 1) × Π[1… n ]′ (f ∘ suc)
-}

[zero:,suc:] = [zero:_,suc:_]
syntax [zero:,suc:] z (λ y → s) = [zero: z ,suc y :→ s ]

Π! : ℕ → ★
Π! n = Π[0… n ] suc

↺ : ℕ → ★
↺ n = Fin n → Fin n

Π!↺ : ∀ {n} → Π! n → ↺ (suc n)
Π!↺ {n} f = inject! ∘ f

Π!↺-inj : ∀ {n}(f : Π! n) → Injective (Π!↺ f)
Π!↺-inj f {x} {y} e = {!!}

-- Move to Type.Identities
module _ {{_ : UA}}{{_ : FunExt}} where
  ΠMaybe : ∀ {A : ★} {F : Maybe A → ★} →
           Π (Maybe A) F ≡ (F nothing × Π A (F ∘ just))
  ΠMaybe {A} {F}
    = (Π (Maybe A) F)
    ≡⟨ Π≃ Maybe≃𝟙⊎ (maybe (λ _ → idp) idp) ⟩
      (Π (𝟙 ⊎ A) [inl: (λ _ → F nothing) ,inr: F ∘ just ])
    ≡⟨ dist-×-Π ⟩
      ((𝟙 → F nothing) × Π A (F ∘ just))
    ≡⟨ ×= 𝟙→A≡A idp ⟩
      (F nothing × Π A (F ∘ just))
    ∎

  ΠFin0≡𝟙 : ∀ {F : Fin 0 → ★} → Π (Fin 0) F ≡ 𝟙
  ΠFin0≡𝟙 = Π= Fin0≡𝟘 (λ()) ∙ Π𝟘-uniq₀ (λ ())

  ΠFin1+ : ∀ n {F : Fin (1 + n) → ★} →
           Π (Fin (1 + n)) F ≡ (F zero × Π (Fin n) (F ∘ suc))
  ΠFin1+ n {F}
    = Π (Fin (1 + n)) F
    ≡⟨ Π≃ Fin∘suc≃𝟙⊎Fin [zero: idp ,suc _ :→ idp ] ⟩
       Π (𝟙 ⊎ Fin n) [inl: (λ _ → F zero) ,inr: F ∘ suc ]
    ≡⟨ dist-×-Π[] ⟩
       ((𝟙 → F zero) × Π (Fin n) (F ∘ suc))
    ≡⟨ ×= 𝟙→A≡A idp ⟩
       (F zero × Π (Fin n) (F ∘ suc))
    ∎

  rot : ∀ {n} → Fin (suc n) → Fin (suc n)
  rot {n} = [zero: ℕ▹Fin n ,suc: inject₁ ]

  ΠFin1+' : ∀ n {F : Fin (1 + n) → ★} →
           Π (Fin (1 + n)) F ≡ (F (ℕ▹Fin n) × Π (Fin n) (F ∘ inject₁))
  ΠFin1+' n {F} =
     Π (Fin (1 + n)) F
    ≡⟨ Π≃ Fin∘suc≃𝟙⊎Fin (λ x → {!WRONG!}) ⟩
     Π (𝟙 ⊎ Fin n) [inl: (λ _ → F {!!}) ,inr: F ∘ {!!} ]
    ≡⟨ {!!} ⟩
     Π (𝟙 ⊎ Fin n) [inl: (λ _ → F (ℕ▹Fin n)) ,inr: F ∘ inject₁ ]
    ≡⟨ dist-×-Π[] ⟩
     ((𝟙 → F (ℕ▹Fin n)) × Π (Fin n) (F ∘ inject₁))
    ≡⟨ ×= 𝟙→A≡A idp ⟩
     (F (ℕ▹Fin n) × Π (Fin n) (F ∘ inject₁))
    ∎

{-
  ΠFin1≡F0 : {F : Fin 1 → ★} → Π (Fin 1) F ≡ F zero
  ΠFin1≡F0 = ΠFin1+ 0 ∙ ×= idp ΠFin0≡𝟙 ∙ A×𝟙≡A

  ΠFin2≡F0×F1 : {F : Fin 2 → ★} → Π (Fin 2) F ≡ (F zero × F (suc zero))
  ΠFin2≡F0×F1 = ΠFin1+ 1 ∙ ×= idp ΠFin1≡F0

  test-Π[0…-1] : ∀ {f} → Π[0… 0 -1] f ≡ 𝟙
  test-Π[0…-1] = ΠFin0≡𝟙

  test-Π[0…0] : ∀ {f} → Π[0… 0 ] f ≡ Fin (f zero)
  test-Π[0…0] = ΠFin1≡F0

  test-Π[0…1] : ∀ {f} → Π[0… 1 ] f ≡ (Fin (f zero) × Fin (f (suc zero)))
  test-Π[0…1] = ΠFin2≡F0×F1

  ΠFin1+ʳ′ : ∀ n (F : ℕ → ★) →
               Π (Fin (1 + n)) (F ∘ Fin▹ℕ) ≡ (F n × Π (Fin n) (F ∘ Fin▹ℕ))
  ΠFin1+ʳ′ n F
      = Π (Fin (1 + n)) (F ∘ Fin▹ℕ)
      ≡⟨ Π=′ (Fin (1 + n)) F∘Fin▹ℕ≗F' ⟩
        Π (Fin (1 + n)) F'
      ≡⟨ ΠFin1+ n ⟩
        (F' zero × Π (Fin n) (F' ∘ suc))
      ≡⟨by-definition⟩
        (F n × Π (Fin n) (F ∘ Fin▹ℕ))
      ∎
    where F' : (x : Fin (suc n)) → ★₀
          F' zero = F n
          F' (suc x) = F (Fin▹ℕ x)
          F∘Fin▹ℕ≗F' : F ∘ Fin▹ℕ ≗ F'
          F∘Fin▹ℕ≗F' zero = {!!}
          F∘Fin▹ℕ≗F' (suc x₂) = {!!}

{-Π (Fin (1 + n)) (F ∘ Fin▹ℕ)
            ≡⟨ {!!} ⟩
               Π (𝟙 ⊎ Fin n) {!!}
            ≡⟨ {!dist-×-Π!} ⟩
               (F n × Π (Fin n) (F ∘ Fin▹ℕ))
            ∎
-}

module _ {{_ : UA}}{{_ : FunExt}} where
  Π≡Π′[0…_-1] : ∀ n f → Π[0… n -1]′ f ≡ Π[0… n -1] f
  Π≡Π′[0… zero  -1] f = ¡ ΠFin0≡𝟙
  Π≡Π′[0… suc n -1] f = Π[0… 1 + n -1]′ f
                     ≡⟨by-definition⟩
                       (Fin (f 0) × Π[0… n -1]′ (f ∘ suc))
                     ≡⟨ ×= idp (Π≡Π′[0… n -1] (f ∘ suc)) ⟩
                       (Fin (f 0) × Π[0… n -1] (f ∘ suc))
                     ≡⟨ ¡ ΠFin1+ n ⟩
                       Π[0… 1 + n -1] f
                     ∎

  Π≡Π′[0…_] : ∀ n f → Π[0… n ]′ f ≡ Π[0… n ] f
  Π≡Π′[0… n ] = Π≡Π′[0… suc n -1]
-- (A → B ⊎ C)

-- TODO
-- adequate! : ∀ n → Fin (suc n) × Fin (n !) ≡ Π (Fin n) (Fin′ ∘ suc)

example : ∀ {n} → (2 + n)! ≡ (2 + n) * (1 + n)!
example = idp

module _ {{_ : UA}}{{_ : FunExt}} where

{-
  -- WRONG
  adequate! : ∀ {n} → Fin (n !) ≡ Π[0… n -1] suc
  adequate! {zero}  = {!¡ ΠFin1≡F0!}
  adequate! {suc n} = (Fin ((1 + n)!))
                    ≡⟨by-definition⟩
                      Fin ((1 + n) * n !)
                    ≡⟨ ¡ Fin-×-* ⟩
                      (Fin (1 + n) × Fin (n !))
                    ≡⟨ ×= idp adequate! ⟩
                      (Fin (1 + n) × Π[0… n -1] suc)
                    ≡⟨ {!ΠFin1+!} ⟩
                      (Fin 1 × Π[0… n -1] (_+_ 2))
                    ≡⟨ ¡ ΠFin1+ n ⟩
                      Π[0… n ] suc
                    ∎
                    -}

  adequate! : ∀ {n} → Fin (n !) ≡ Π[0… n ] suc
  adequate! {zero}  = ¡ ΠFin1≡F0
  adequate! {suc n} = (Fin ((1 + n)!))
                    ≡⟨by-definition⟩
                      Fin ((1 + n) * n !)
                    ≡⟨ ¡ Fin-×-* ⟩
                      (Fin (1 + n) × Fin (n !))
                    ≡⟨ ×= idp adequate! ⟩
                      (Fin (1 + n) × Π[0… n ] suc)
                    ≡⟨ ¡ ΠFin1+ʳ′ (suc n) _ ⟩
                      ((x : Fin (2 + n)) → Fin (suc (Fin▹ℕ x)))
                    ≡⟨ idp ⟩
                      Π[0… 1 + n ] suc
                    ∎

{-
  adequate! : ∀ {n} → Fin ((1 + n)!) ≡ Π[0… n -1] suc
  adequate! {zero}  = {!idp!}
  adequate! {suc n} = (Fin ((2 + n)!))
                    ≡⟨ {!!} ⟩
                      Fin ((1 + n) * (1 + n)!)
                    ≡⟨ ¡ Fin-×-* ⟩
                      (Fin (1 + n) × Fin ((1 + n)!))
                    ≡⟨ ×= idp adequate! ⟩
                      (Fin (1 + n) × Π[0… n -1] suc)
                    ≡⟨ ¡ (ΠFin1+ʳ′ n (Fin ∘ suc)) ⟩
                      Π[0… suc n -1] suc
                    ∎
-}
{-

HI: (n+1)! ≡ Π n suc

(n+2)!
(n+2) * (n+1)!
(n+2) * Π n suc
(n+1) * Π n suc + Π n suc

(2+n)*(n! * 1+n) 
(n! * 1+n) + (1+n)*(n! * 1+n) 

≡ Π n (2+)
≡ 1 × Π n (2+)


(2+n) * Π n suc
Π (1+n) suc

-- -}
-- -}
-- -}
-- -}
-- -}
