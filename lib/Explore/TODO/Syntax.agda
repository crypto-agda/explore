{-# OPTIONS --without-K #-}
open import Type
open import Data.Bits    using (Bits)
open import Data.Bit     using (Bit)
open import Data.Zero   using (𝟘)
open import Data.Fin     using (Fin)
open import Data.Maybe   using (Maybe)
open import Data.Nat     using (ℕ)
open import Data.Product using (Σ; _×_)
open import Data.Sum     using (_⊎_)
open import Data.One    using (𝟙)
open import Data.Vec     using (Vec)

module Explore.Syntax where

-- this is to be imported from the appropriate module
postulate
  S : ★₀ → ★₀
  S𝟙 : S 𝟙
  SBit : S Bit
  SFin : ∀ n → S (Fin n)
  SBits : ∀ n → S (Bits n)
  SVec : ∀ {A} → S A → ∀ n → S (Vec A n)
  _S×_ : ∀ {A B} → S A → S B → S (A × B)
  _S⊎_ : ∀ {A B} → S A → S B → S (A ⊎ B)
  SMaybe : ∀ {A} → S A → S (Maybe A)
  SΣ : ∀ {A} {B : A → _} → S A → (∀ x → S (B x)) → S (Σ A B)
  S𝟙→ : ∀ {A} → S A → S (𝟙 → A)
  SBit→ : ∀ {A} → S A → S (Bit → A)
  S𝟘→ : ∀ A → S (𝟘 → A)
  S×→ : ∀ {A B C} → S (A → B → C) → S (A × B → C)
  S⟨_⊎_⟩→ : ∀ {A B C} → S (A → C) → S (B → C) → S (A ⊎ B → C)

module Fin-universe where

    `★ : ★₀
    `★ = ℕ

    -- decoding
    El : `★ → ★₀
    El = Fin

    `S : ∀ `A → S (El `A)
    `S = SFin

module Bits-universe where

    `★ : ★₀
    `★ = ℕ

    -- decoding
    El : `★ → ★₀
    El = Bits

    `S : ∀ `A → S (El `A)
    `S = SBits

module ⊎×-universe where

    data `★ : ★₀ where
      `𝟙 : `★
      _`×_ _`⊎_ : `★ → `★ → `★

    -- decoding
    El : `★ → ★₀
    El `𝟙 = 𝟙
    El (s `× t) = El s × El t
    El (s `⊎ t) = El s ⊎ El t

    `S : ∀ `A → S (El `A)
    `S `𝟙       = S𝟙
    `S (s `× t) = `S s S× `S t
    `S (s `⊎ t) = `S s S⊎ `S t

module 𝟙-Maybe-universe where

    data `★ : ★₀ where
      -- one element
      `𝟙     : `★
      -- one element more
      `Maybe : `★ → `★

    -- decoding
    El : `★ → ★₀
    El `𝟙 = 𝟙
    El (`Maybe t) = Maybe (El t)

    `S : ∀ `A → S (El `A)
    `S `𝟙 = S𝟙
    `S (`Maybe t) = SMaybe (`S t)

module ΣBit-universe where

    data `★ : ★₀
    El : `★ → ★₀

    data `★ where
      `Bit : `★
      `Σ   : (s : `★) → (El s → `★) → `★

    -- decoding
    El `Bit     = Bit
    El (`Σ s t) = Σ (El s) λ x → El (t x)

    `S : ∀ `A → S (El `A)
    `S `Bit = SBit
    `S (`Σ s t) = SΣ (`S s) λ x → `S (t x)

module ⊎×→-universe where

    -- Types appearing on the left of an arrow
    data `★⁻ : ★₀ where
      -- zero and elements
      `𝟘 `𝟙 : `★⁻

      -- products and co-products
      _`×_ _`⊎_ : `★⁻ → `★⁻ → `★⁻

    -- decoding of negative types
    El⁻ : `★⁻ → ★₀
    El⁻ `𝟘 = 𝟘
    El⁻ `𝟙 = 𝟙
    El⁻ (s `× t) = El⁻ s × El⁻ t
    El⁻ (s `⊎ t) = El⁻ s ⊎ El⁻ t

    `S⟨_⟩→_ : ∀ `A {B} (sB : S B) → S (El⁻ `A → B)
    `S⟨ `𝟘 ⟩→ t = S𝟘→ _
    `S⟨ `𝟙 ⟩→ t = S𝟙→ t
    `S⟨ s `× t ⟩→ u = S×→ (`S⟨ s ⟩→ `S⟨ t ⟩→ u)
    `S⟨ s `⊎ t ⟩→ u = S⟨ `S⟨ s ⟩→ u ⊎ `S⟨ t ⟩→ u ⟩→

    data `★ : ★₀ where
      -- one element
      `𝟙     : `★

      -- products and co-products
      _`×_ _`⊎_ : `★ → `★ → `★

      -- functions
      _`→_ : `★⁻ → `★ → `★

    -- decoding of positive types
    El : `★ → ★₀
    El `𝟙 = 𝟙
    El (s `× t) = El s × El t
    El (s `⊎ t) = El s ⊎ El t
    El (s `→ t) = El⁻ s → El t

    `S : ∀ `A → S (El `A)
    `S `𝟙 = S𝟙
    `S (s `× t) = `S s S× `S t
    `S (s `⊎ t) = `S s S⊎ `S t
    `S (s `→ t) = `S⟨ s ⟩→ `S t

module Σ⊎×→-universe where

    -- Types appearing on the left of an arrow
    data `★⁻ : ★₀ where
      -- zero, one, and two elements
      `𝟘 `𝟙 `Bit : `★⁻

      -- products and co-products
      _`×_ _`⊎_ : `★⁻ → `★⁻ → `★⁻

      -- Σ?

    -- decoding of negative types
    El⁻ : `★⁻ → ★₀
    El⁻ `𝟘 = 𝟘
    El⁻ `𝟙 = 𝟙
    El⁻ `Bit = Bit
    El⁻ (s `× t) = El⁻ s × El⁻ t
    El⁻ (s `⊎ t) = El⁻ s ⊎ El⁻ t

    `S⟨_⟩→_ : ∀ `A {B} (sB : S B) → S (El⁻ `A → B)
    `S⟨ `𝟘 ⟩→ t = S𝟘→ _
    `S⟨ `𝟙 ⟩→ t = S𝟙→ t
    `S⟨ `Bit ⟩→ t = SBit→ t
    `S⟨ s `× t ⟩→ u = S×→ (`S⟨ s ⟩→ `S⟨ t ⟩→ u)
    `S⟨ s `⊎ t ⟩→ u = S⟨ `S⟨ s ⟩→ u ⊎ `S⟨ t ⟩→ u ⟩→

    data `★ : ★₀
    El : `★ → ★₀

    data `★ where
      -- one and two elements
      `𝟙 `Bit : `★

      -- 'n' elements
      `Fin : ℕ → `★

      -- one element more
      `Maybe : `★ → `★

      -- products and co-products
      _`×_ _`⊎_ : `★ → `★ → `★

      -- dependent pairs
      `Σ   : (s : `★) → (El s → `★) → `★

      -- vectors
      `Vec : `★ → ℕ → `★

      -- functions
      _`→_ : `★⁻ → `★ → `★

    -- decoding of positive types
    El `𝟙 = 𝟙
    El `Bit = Bit
    El (`Fin n) = Fin n
    El (`Maybe t) = Maybe (El t)
    El (s `× t) = El s × El t
    El (s `⊎ t) = El s ⊎ El t
    El (`Σ s t) = Σ (El s) λ x → El (t x)
    El (s `→ t) = El⁻ s → El t
    El (`Vec t n) = Vec (El t) n

    `Bits = `Vec `Bit

    `S : ∀ `A → S (El `A)
    `S `𝟙 = S𝟙
    `S `Bit = SBit
    `S (`Fin n) = SFin n
    `S (`Maybe `A) = SMaybe (`S `A)
    `S (`A `× `B) = `S `A S× `S `B
    `S (`A `⊎ `B) = `S `A S⊎ `S `B
    `S (`Σ `A `B) = SΣ (`S `A) λ x → `S (`B x)
    `S (`Vec `A n) = SVec (`S `A) n
    `S (`A `→ `B) = `S⟨ `A ⟩→ `S `B
