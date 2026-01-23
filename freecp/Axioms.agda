{-# OPTIONS --rewriting --guardedness #-}
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  extensionality  : ∀{A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
  excluded-middle : (P : Set) → P ⊎ ¬ P
