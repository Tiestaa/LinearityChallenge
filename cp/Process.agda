{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}
open import Data.List.Base using ([]; _∷_; _++_; [_])
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Type
open import Context
open import Permutations

data Proc : Context → Set where
    {-- Axiom (Ax) --}
    link : ∀{A} → Proc (dual A ∷ A ∷ [])

    {-- Parallel Composition - Cut --}
    cut  : ∀{Γ Δ Θ A} → 
        Γ ≃ Δ + Θ → 
        Proc (A ∷ Δ) → 
        Proc (dual A ∷ Θ) → 
        Proc Γ

    {-- Output - Fork --}
    fork : ∀{Γ Δ Θ A B} →  
        Γ ≃ Δ + Θ →
        (i : (A ⊗ B)  ∈` Θ) →
        Proc (A ∷ Δ) → 
        Proc (update Θ B i) → 
        Proc Γ

    {-- Input - Join --}
    join : ∀{Γ A B} →
        (i : ( A ⅋ B ) ∈` Γ) → 
        Proc (A ∷ update Γ B i) → 
        Proc Γ

    {-- Input selection - Left --}
    select-l : ∀{Γ A B} →
        (i : (A ⊕ B) ∈` Γ) → 
        Proc (update Γ A i) →
        Proc Γ

    {-- Input selection - Right --}
    select-r : ∀{Γ A B} →
        (i : (A ⊕ B) ∈` Γ) → 
        Proc (update Γ B i) →
        Proc Γ

    {-- Choice --}
    case : ∀{Γ A B} →
        (i : (A & B) ∈` Γ) →
        Proc (update Γ A i) → 
        Proc (update Γ B i) →
        Proc Γ 
    
    {-- Server --}
    server : ∀{Γ A} →
        (i :  `! A  ∈`  Γ) →
        Un (delete Γ i) →      
        Proc (A ∷ delete Γ i) → 
        Proc Γ
        
    {-- Client --}    
    client : ∀{Γ A} →
        (i : `? A ∈` Γ) →
        Proc (A ∷ delete Γ i) →
        Proc Γ

    {-- Weaken --}
    weaken : ∀{Γ A} →
        (i : `? A ∈` Γ) →
        Proc (delete Γ i) →
        Proc Γ

    {-- Contract --}
    contract : ∀{Γ A} → 
        (i : `? A ∈` Γ) →
        Proc (`? A ∷ Γ) → 
        Proc Γ

    {-- Exists --}
    ex : ∀{Γ B} → 
        (i : `∃ B ∈` Γ) →
        (A : Type) →
        Proc ( update Γ (subst [ A /] B) i) → 
        Proc Γ

    {-- All --}
    all : ∀{Γ B} → 
        (i : `∀ B ∈` Γ) → 
        ((A : Type) → Proc (update Γ (subst [ A /] B) i))→ 
        Proc Γ

    {-- Close - 𝟙 --}
    close : ∀{Γ} →
        Γ ≡ [ 𝟙 ] →
        Proc Γ

    {-- Wait - ⊥ --}
    wait : ∀{Γ} →
        (i : ⊥ ∈` Γ ) →
        Proc (delete Γ i) →
        Proc Γ

    {-- Fail - ⊤ --}
    fail : ∀{Γ} →
        (i : ⊤ ∈` Γ) →
        Proc Γ 


↔proc : ∀{Γ Δ} → Γ ↔ Δ → Proc Γ → Proc Δ
↔proc π γ = {!   !}