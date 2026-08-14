{-# OPTIONS --rewriting #-}
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (refl)

open import Type
open import Context
open import Process
open import Reduction
open import Congruence

data Link : ∀{Γ} → Proc Γ → Set where
    link : ∀{A} → Link (link {A})

data Input : ∀{Γ} → Proc Γ → Set where
    fail : ∀{Γ} → Input (fail (here {Γ = Γ}))
    wait : ∀{Γ P}   → Input (wait (here {Γ = Γ}) P)
    -- case : ∀{P Q} → Input (case here here P Q)
    -- join : ∀{P}   → Input (join here P)