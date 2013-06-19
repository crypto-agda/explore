module factorial where

open import Type
open import Data.Nat.NP
open import Data.Product
open import Data.Sum
open import Data.Zero
open import Data.One
open import Data.Fin using (Fin; Fin′; zero; suc; inject₁)
                     renaming (toℕ to Fin▹ℕ; fromℕ to ℕ▹Fin)
open import Function.NP as F
open import Function.Related as FR
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as I
open I using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.Sum
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

module v1 where

    -- n ! ≡ product [1..n]
    _! : ℕ → ℕ
    zero  ! = 1
    suc n ! = (1 + n) * n !

    {-
    data _!★ : ℕ → ★ where
      zero : {-𝟙 →-} zero !★
      suc  : ∀ {n} → (n !★ × Fin n) → (suc n)!★
    -}

    _!★ : ℕ → ★
    zero  !★ = 𝟙
    suc n !★ = Fin (1 + n) × n !★

    !★≅Fin! : ∀ n → n !★ ↔ Fin (n !)
    !★≅Fin! zero    = I.sym Fin1↔⊤
    !★≅Fin! (suc n) = Fin-×-* (suc n) (n !) I.∘ I.id ×-cong !★≅Fin! n

module v2 where
    -- n ! ≡ product [1..n]
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

    !★≅Fin! : ∀ n → n !★ ↔ Fin (n !)
    !★≅Fin! zero    = I.sym Fin1↔⊤
    !★≅Fin! (suc n) = Fin-⊎-+ (n !) (n * n !)
                  I.∘ !★≅Fin! n ⊎-cong
                      (Fin-×-* n (n !) I.∘ I.id ×-cong !★≅Fin! n)

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

test-product[1…3] : product[1… 3 ] ≡ (λ f → f 1 * (f 2 * (f 3 * 1)))
test-product[1…3] = ≡.refl

open v1
adequate1 : ∀ n → n ! ≡ product[1… n ] id
adequate1 zero = ≡.refl
adequate1 (suc n) rewrite adequate1 n = {!!}
  Π{x∈1…n}x + n * Π{x∈1…n}x

  (1 + n) * Π{x∈1…n}x

  Π{x∈1…n}1+x

{-
open import Data.Maybe
ΠMaybe : ∀ {A : ★} {F : Maybe A → ★} →
         Π (Maybe A) F ↔ F nothing × Π A (F ∘ just)
ΠMaybe = {!!}
-}

ΠFin1+ : ∀ n (F : Fin (1 + n) → ★) →
         Π (Fin (1 + n)) F ↔ (F zero × Π (Fin n) (F ∘ suc))
ΠFin1+ = {!!}

ΠFin1+′ : ∀ n (F : ℕ → ★) →
         Π (Fin (1 + n)) (F ∘ Fin▹ℕ) ↔ (F zero × Π (Fin n) (F ∘ suc ∘′ Fin▹ℕ))
ΠFin1+′ = {!!}

ΠFin1+ʳ : ∀ n (F : Fin (1 + n) → ★) →
         Π (Fin (1 + n)) F ↔ (F (ℕ▹Fin n) × Π (Fin n) (F ∘ inject₁))
ΠFin1+ʳ = {!!}

ΠFin1+ʳ′ : ∀ n (F : ℕ → ★) →
           Π (Fin (1 + n)) (F ∘ Fin▹ℕ) ↔ (F n × Π (Fin n) (F ∘ Fin▹ℕ))
ΠFin1+ʳ′ = {!!}

Π[0…_] : ℕ → (ℕ → ℕ) → ★
Π[0… n ] f = Π (Fin n) (Fin ∘ f ∘ Fin▹ℕ)

Π[0…_]′ : ℕ → (ℕ → ℕ) → ★
Π[0… zero  ]′ f = 𝟙
Π[0… suc n ]′ f = Fin (f 0) × Π[0… n ]′ (f ∘ suc)

Π[1…_]′ : ℕ → (ℕ → ℕ) → ★
Π[1… zero  ]′ f = 𝟙
Π[1… suc n ]′ f = Fin (f 1) × Π[1… n ]′ (f ∘ suc)

-- same as ΠFin0↔𝟙
-- Π𝟘↔𝟙 : ∀ {F : 𝟘 → ★} → Π 𝟘 F ↔ 𝟙
-- Π𝟘↔𝟙 = {!!}

ΠFin0↔𝟙 : ∀ {F : Fin 0 → ★} → Π (Fin 0) F ↔ 𝟙
ΠFin0↔𝟙 = inverses _ (const (λ())) (λ x → {!!}) (λ x → ≡.refl)

Π↔Π′[0…_] : ∀ n f → Π[0… n ]′ f ↔ Π[0… n ] f
Π↔Π′[0… zero  ] f = I.sym ΠFin0↔𝟙
Π↔Π′[0… suc n ] f = Π[0… 1 + n ]′ f
                  ↔⟨ I.id ⟩
                    (Fin (f 0) × Π[0… n ]′ (f ∘ suc))
                  ↔⟨ I.id ×-cong Π↔Π′[0… n ] (f ∘ suc) ⟩
                    (Fin (f 0) × Π[0… n ] (f ∘ suc))
                  ↔⟨ I.sym (ΠFin1+′ n (Fin ∘ f)) ⟩
                    Π[0… 1 + n ] f
                  ∎
                where open FR.EquationalReasoning

-- (A → B ⊎ C)

-- TODO
-- adequate! : ∀ n → Fin (suc n) × Fin (n !) ↔ Π (Fin n) (Fin′ F.∘ suc)

foo : ∀ n → (2 + n)! ≡ (2 + n) * (1 + n)!
foo = λ n → ≡.refl

adequate! : ∀ n → Fin ((1 + n)!) ↔ Π[0… n ] suc
adequate! zero = {!I.id!}
adequate! (suc n) = (Fin ((2 + n)!))
                  ↔⟨ {!!} ⟩
                    Fin ((1 + n) * (1 + n)!)
                  ↔⟨ I.sym (Fin-×-* (1 + n) (suc n !)) ⟩
                    (Fin (1 + n) × Fin ((1 + n)!))
                  ↔⟨ I.id ×-cong adequate! n ⟩
                    (Fin (1 + n) × Π[0… n ] suc)
                  ↔⟨ I.sym (ΠFin1+ʳ′ n (Fin ∘ suc)) ⟩
                    Π[0… suc n ] suc
                  ∎
                where open FR.EquationalReasoning
{-

HI: (n+1)! ↔ Π n suc

(n+2)!
(n+2) * (n+1)!
(n+2) * Π n suc
(n+1) * Π n suc + Π n suc

(2+n)*(n! * 1+n) 
(n! * 1+n) + (1+n)*(n! * 1+n) 

↔ Π n (2+)
↔ 1 × Π n (2+)


(2+n) * Π n suc
Π (1+n) suc

-- -}
