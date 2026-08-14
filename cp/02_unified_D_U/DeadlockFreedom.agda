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
    fail : ∀{Γ}     → Input (fail (here {Γ = Γ}))
    wait : ∀{Γ P}   → Input (wait (here {Γ = Γ}) P)
    case : ∀{Γ A B} (P : Proc (A ∷ Γ)) (Q : Proc (B ∷ Γ)) → Input (case (here {Γ = Γ}) (here {Γ = Γ}) P Q)
    join : ∀{Γ A B}  (P : Proc (A ∷ B ∷ Γ)) → Input (join (here {Γ = Γ}) P)

data Output : ∀{Γ} → Proc Γ → Set where
    close    : Output close
    select-l : ∀{Γ A B} (P : Proc (A ∷ Γ)) →  Output (select-l {B = B} here P)
    select-r : ∀{Γ A B} (P : Proc (B ∷ Γ)) →  Output (select-r {A = A} here P)
    fork : ∀{Γ Δ Θ A B} {P : Proc (A ∷ Δ)} {Q : Proc (B ∷ Θ)} (σ : Γ ≃ Δ + ((A ⊗ B) ∷ Θ)) → Output (fork σ here P Q)

data Delayed : ∀{Γ} → Proc Γ → Set where
    fail     : ∀{Γ Δ C} {U : Update  ⊤  [] Γ Δ} → Delayed (fail (next {C = C} U))
    wait     : ∀{Γ Δ C P} {U : Update (⊥) [] Γ Δ} → Delayed (wait (next {C = C} U) P)
    case     : ∀{Γ Δ C P Q A B} {U : Update (A & B) [ A ] Γ Δ} {U` : Update ((A & B)) [ B ] Γ Δ} → Delayed (case (next {C = C} U) (next {C = C} U`) P Q)
    select-l : ∀{Γ Δ C P A B} {U : Update (A ⊕ B) [ A ] Γ Δ} → Delayed (select-l (next {C = C} U) P)
    select-r : ∀{Γ Δ C P A B} {U : Update (A ⊕ B) [ B ] Γ Δ}→ Delayed (select-r (next {C = C} U) P)
    join     : ∀{Γ Δ C A B} {U : Update (A ⅋ B) [ B ] Γ Δ} (P : Proc (A ∷ C ∷ Δ)) → Delayed (join (next {C = C} U) P)
    fork-l   : ∀{Γ Δ Θ A B C Θ` P Q} {U : Update (A ⊗ B) [ B ] Θ Θ`} (σ : Γ ≃ Δ + Θ)  → Delayed (fork (<_ {C} σ) U P Q)
    fork-r   : ∀{Γ Δ Θ A B C Θ` P Q} {U : Update (A ⊗ B) [ B ] Θ Θ`} (σ : Γ ≃ Δ + Θ) → Delayed (fork (> σ) (next {C = C} U) P Q) 

data Server : ∀{Γ} → Proc Γ → Set where

data DelayedServer : ∀{Γ} → Proc Γ → Set where

data Thread {Γ} (P : Proc Γ) : Set where
  link    : Link P → Thread P
  delayed : Delayed P → Thread P
  output  : Output P → Thread P
  input   : Input P → Thread P
  server  : Server P → Thread P
  dserver : DelayedServer P → Thread P

Observable : ∀{Γ} → Proc Γ → Set
Observable P = ∃[ Q ] P ⊒ Q × Thread Q

Reducible : ∀{Γ} → Proc Γ → Set
Reducible P = ∃[ Q ] P ↝ Q

Alive : ∀{Γ} → Proc Γ → Set
Alive P = Observable P ⊎ Reducible P


fork→thread : ∀{Γ Δ Θ A B Θ` P Q} (σ : Γ ≃ Δ + Θ) (U : Update (A ⊗ B) [ B ] Θ Θ`) → Thread (fork σ U P Q)
fork→thread (< σ) U        = delayed (fork-l σ)
fork→thread (> σ) here     = output (fork (> σ))
fork→thread (> σ) (next _) = delayed (fork-r σ)

join→thread : ∀{Γ Δ A B P} (U : Update (A ⅋ B) [ B ] Γ Δ) → Thread (join U P)
join→thread here     = input (join _)
join→thread (next _) = delayed (join _)

fail→thread : ∀{Γ Δ} → (U : Update (⊤) [] Γ Δ) → Thread (fail U)
fail→thread here     = input fail
fail→thread (next _) = delayed (fail)

case→thread : ∀{Γ A B Δ Δ` P Q} → (U : Update (A & B) [ A ] Γ Δ) → (U` : Update (A & B) [ B ] Γ Δ`) → Thread (case U U` P Q)
case→thread here here = input (case _ _)
case→thread here (next U`) = {!   !}
case→thread (next U) here = {!   !}
case→thread (next U) (next U`) = delayed {!   !}

wait→thread : ∀{Γ Δ P} → (U : Update (⊥) [] Γ Δ) → Thread (wait U P)
wait→thread here     = input wait
wait→thread (next _) = delayed wait

select-l→thread : ∀{ Γ Δ A B P} → (U : Update (A ⊕ B) [ A ] Γ Δ) → Thread (select-l U P)
select-l→thread here     = output (select-l _)
select-l→thread (next U) = delayed select-l

select-r→thread : ∀{ Γ Δ A B P} → (U : Update (A ⊕ B) [ B ] Γ Δ) → Thread (select-r U P)
select-r→thread here     = output (select-r _)
select-r→thread (next U) = delayed select-r

deadlock-freedom : ∀{Γ} (P : Proc Γ) → Alive P
deadlock-freedom link            = inj₁ (_ , s-refl , link link)
deadlock-freedom (fork σ U _ _)  = inj₁ (_ , s-refl , fork→thread σ U)
deadlock-freedom (join U _)      = inj₁ (_ , s-refl , join→thread U)
deadlock-freedom (select-l U _)  = inj₁ (_ , s-refl , select-l→thread U)
deadlock-freedom (select-r U P)  = inj₁ (_ , s-refl , select-r→thread U)
deadlock-freedom (case U U` _ _) = inj₁ (_ , s-refl , case→thread U U`)
deadlock-freedom close           = inj₁ (_ , s-refl , output close)
deadlock-freedom (wait U _)      = inj₁ (_ , s-refl , wait→thread U)
deadlock-freedom (fail U)        = inj₁ (_ , s-refl , fail→thread U)
deadlock-freedom (cut x P P₁) = {!   !}