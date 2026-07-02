{-# OPTIONS --rewriting #-}

open import Type
open import Context
open import Permutations
open import Process

postulate
  Name    : Type
  Credit  : Type
  Receipt : Type

Buy : Type
Buy = Name ⊗ (Credit ⊗ (dual Receipt ⅋ ⊥))

Sell : Type
Sell = dual Name ⅋ (dual Credit ⅋ (Receipt ⊗ 𝟙))
