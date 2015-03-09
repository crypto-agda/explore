{-# OPTIONS --without-K #-}
module Explore.GroupHomomorphism where

open import Level
open import Algebra.FunctionProperties
open import Data.Product
open import Function using (_∘_ ; flip)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Relation.Binary.PropositionalEquality.NP hiding (_∙_)

open import Explore.Core
open import Explore.Properties
open import Explore.Sum

{-
 I had some problems with using the standard library definiton of Groups
 so I rolled my own, therefor I need some boring proofs first

-}
record Group (G : Set) : Set where
  field
    _∙_ : G → G → G
    ε   : G
    -_  : G → G

  -- laws
  field
    assoc    : Associative _≡_ _∙_
    identity : Identity _≡_ ε _∙_
    inverse  : Inverse _≡_ ε -_ _∙_

  -- derived property
  help : ∀ x y → x ≡ (x ∙ y) ∙ - y
  help x y = x
           ≡⟨ ! proj₂ identity x ⟩
             x ∙ ε
           ≡⟨ ap (_∙_ x) (! proj₂ inverse y) ⟩
             x ∙ (y ∙ - y)
           ≡⟨ ! assoc x y (- y) ⟩
             (x ∙ y) ∙ (- y)
           ∎
    where open ≡-Reasoning

  unique-1g : ∀ x y → x ∙ y ≡ y → x ≡ ε
  unique-1g x y eq = x
                   ≡⟨ help x y ⟩
                     (x ∙ y) ∙ - y
                   ≡⟨ ap (flip _∙_ (- y)) eq ⟩
                     y ∙ - y
                   ≡⟨ proj₂ inverse y ⟩
                     ε
                   ∎
    where open ≡-Reasoning

  unique-/ : ∀ x y → x ∙ y ≡ ε → x ≡ - y
  unique-/ x y eq = x
                  ≡⟨ help x y ⟩
                    (x ∙ y) ∙ - y
                  ≡⟨ ap (flip _∙_ (- y)) eq ⟩
                    ε ∙ - y
                  ≡⟨ proj₁ identity (- y) ⟩
                    - y
                  ∎
    where open ≡-Reasoning

module _ {A B : Set}(GA : Group A)(GB : Group B) where
  open Group GA using (-_;inverse;identity) renaming (_∙_ to _+_; ε to 0g)
  open Group GB using (unique-1g ; unique-/) renaming (_∙_ to _*_; ε to 1g; -_ to 1/_)

  GroupHomomorphism : (A → B) → Set
  GroupHomomorphism f = ∀ x y → f (x + y) ≡ f x * f y

  module GroupHomomorphismProp {f}(f-homo : GroupHomomorphism f) where
    f-pres-ε : f 0g ≡ 1g
    f-pres-ε = unique-1g (f 0g) (f 0g) part
      where open ≡-Reasoning
            part = f 0g * f 0g
                 ≡⟨ ! f-homo 0g 0g ⟩
                   f (0g + 0g)
                 ≡⟨ ap f (proj₁ identity 0g) ⟩
                   f 0g
                 ∎

    f-pres-inv : ∀ x → f (- x) ≡ 1/ f x
    f-pres-inv x = unique-/ (f (- x)) (f x) part
      where open ≡-Reasoning
            part = f (- x) * f x
                 ≡⟨ ! f-homo (- x) x ⟩
                   f (- x + x)
                 ≡⟨ ap f (proj₁ inverse x) ⟩
                   f 0g
                 ≡⟨ f-pres-ε ⟩
                   1g
                 ∎

module _ {A B}(GA : Group A)(GB : Group B)
         (f : A → B)
         (exploreA : Explore zero A)(f-homo : GroupHomomorphism GA GB f)
         ([f] : B → A)(f-sur : ∀ b → f ([f] b) ≡ b)
         (explore-ext : ExploreExt exploreA)
         where
  open Group GA using (-_) renaming (_∙_ to _+_ ; ε to 0g)
  open Group GB using ()   renaming (_∙_ to _*_ ; ε to 1g ; -_ to 1/_)
  open GroupHomomorphismProp GA GB f-homo

  {- How all this is related to elgamal

  the Group GA is ℤq with modular addition as operation
  the Group GB is the cyclic group with order q

  f is g^, the proof only need that it is a group homomorphism
  and that it has a right inverse

  we require that the explore (for type A) function (should work with only summation)
  is Stable under addition of GA (notice that we have flip in there that is so that
  we don't need commutativity

  finally we require that the explore function respects extensionality
  -}

  {-
    While this proof looks complicated it basically just adds inverse of m₀ and then adds m₁ (from image of f)
    we need the homomorphic property to pull out the values.

  -}

  module _ {X}(z : X)(op : X → X → X)
           (sui : ∀ k → StableUnder' exploreA z op (flip (Group._∙_ GA) k))
    where
  -- this proof isn't actually any hard..
    thm : ∀ (O : B → X) m₀ m₁ → exploreA z op (λ x → O (f x * m₀)) ≡ exploreA z op (λ x → O (f x * m₁))
    thm O m₀ m₁ = explore (λ x → O (f x * m₀))
                 ≡⟨ sui (- [f] m₀) (λ x → O (f x * m₀)) ⟩
                   explore (λ x → O (f (x + - [f] m₀)  * m₀))
                 ≡⟨ explore-ext z op (λ x → ap O (lemma1 x)) ⟩
                   explore (λ x → O (f x ))
                 ≡⟨ sui ([f] m₁) (O ∘ f) ⟩
                   explore (λ x → O (f (x + [f] m₁)))
                 ≡⟨ explore-ext z op (λ x → ap O (lemma2 x)) ⟩
                   explore (λ x → O (f x * m₁))
                 ∎
     where
      open ≡-Reasoning
      explore = exploreA z op

      lemma1 : ∀ x → f (x + - [f] m₀) * m₀ ≡ f x
      lemma1 x rewrite f-homo x (- [f] m₀)
                     | f-pres-inv ([f] m₀)
                     | f-sur m₀
                     | Group.assoc GB (f x) (1/ m₀) m₀
                     | proj₁ (Group.inverse GB) m₀
                     | proj₂ (Group.identity GB) (f x) = refl

      lemma2 : ∀ x → f (x + [f] m₁) ≡ f x * m₁
      lemma2 x rewrite f-homo x ([f] m₁)
                     | f-sur m₁ = refl
