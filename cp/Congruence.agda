{-# OPTIONS --rewriting #-}
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_ ; proj₂)
open import Data.List.Base using ([]; _∷_; [_])

open import Type
open import Context
open import Permutations
open import Process

data _⊒_ {Γ} : Proc Γ → Proc Γ → Set where
    s-comm :
        ∀{Γ₁ Γ₂ A} 
        {P : Proc (A ∷ Γ₁)} 
        {Q : Proc (dual A ∷ Γ₂)} 
        (σ : Γ ≃ Γ₁ + Γ₂) →
            cut σ P Q ⊒ cut (+-comm σ) Q P 

    {-- s-link is useless, link is an axiom and can be used ↭proc swap --}

    s-fail :
        ∀{Γ₁ Γ₂ Δ P} 
        (σ  : Γ ≃ Γ₁ + Γ₂)  → 
        (D : Delete Γ₁ ⊤ Δ) →
        let 
            _ , _ , D₁ = ≃-delete-l σ D
        in
        cut σ (fail here) P ⊒ fail D₁

    s-wait :
        ∀{Γ₁ Γ₂ Δ₁ A}            →
        {P : Proc (A ∷ Δ₁)}      →
        {Q : Proc (dual A ∷ Γ₂)} → 
        (σ : Γ ≃ Γ₁ + Γ₂)        →
        (D : Delete Γ₁ ⊥ Δ₁)     →
        let
            _ , σ₁ , D₁ = ≃-delete-l σ D
        in
        cut σ (wait (next D) P) Q ⊒ wait D₁ (cut σ₁ P Q)
    
    s-case : 
        ∀{Γ₁ Γ₂ Δ₁ Δ₂ A B C}          →
        {P : Proc (A ∷ Δ₁)}           →
        {Q : Proc (A ∷ Δ₂)}           →
        {R : Proc (dual A ∷ Γ₂)}      →
        (σ : Γ ≃ Γ₁ + Γ₂)             →
        (U₁ : Update Γ₁ (B & C) B Δ₁) →
        (U₂ : Update Γ₁ (B & C) C Δ₂) →
        let 
            _ , σ₁ , U₃ = ≃-update-l σ U₁
            _ , σ₂ , U₄ = ≃-update-l σ U₂
        in
        cut σ (case (next U₁) (next U₂) P Q) R ⊒ case U₃ U₄ (cut σ₁ P R) (cut σ₂ Q R)

    s-select-l :
        ∀{Γ₁ Γ₂ Δ₁ A B}              →
        {P : Proc (A ∷ Δ₁)}          →
        {Q : Proc (dual A ∷ Γ₂)}     → 
        (σ : Γ ≃ Γ₁ + Γ₂)            →
        (U : Update Γ₁ (A ⊕ B) A Δ₁) →
        let 
            _ , σ₁ , U₁ = ≃-update-l σ U 
        in
        cut σ (select-l (next U) P) Q ⊒ select-l U₁ (cut σ₁ P Q)

    s-select-r :
        ∀{Γ₁ Γ₂ Δ₁ A B}              →
        {P : Proc (A ∷ Δ₁)}          →
        {Q : Proc (dual A ∷ Γ₂)}     → 
        (σ : Γ ≃ Γ₁ + Γ₂)            →
        (U : Update Γ₁ (A ⊕ B) B Δ₁) →
        let 
            _ , σ₁ , U₁ = ≃-update-l σ U 
        in
        cut σ (select-r (next U) P) Q ⊒ select-r U₁ (cut σ₁ P Q)

    s-join :
        ∀{Γ₁ Γ₂ Δ₁ A B C}            →
        {P : Proc (A ∷ C ∷ Δ₁)}      →
        {Q : Proc (dual C ∷ Γ₂)}     → 
        (σ : Γ ≃ Γ₁ + Γ₂)            →
        (U : Update Γ₁ (A ⅋ B) B Δ₁) →
        let 
            _ , σ₁ , U₁ = ≃-update-l σ U 
        in
        cut σ (join (next U) P) Q ⊒ join U₁ (cut (< σ₁) (↭proc swap P) Q)

    s-fork-l :
        ∀{Δ Θ Θ₁ Θ₂ Θ₃ A B C}        →
        {P : Proc (C ∷ Δ)}           →
        {Q : Proc (dual C ∷ A ∷ Θ₁)} →
        {R : Proc Θ₃}                → 
        (σ  : Γ ≃ Δ  + Θ )           →
        (σ₁ : Θ ≃ Θ₁ + Θ₂)           → 
        (U : Update Θ₂ (A ⊗ B) B Θ₃) →
        let 
            δ₁ , σ₃ , σ₄ = +-assoc-r σ σ₁
        in
        cut σ P (fork (< σ₁) U (↭proc swap Q) R) ⊒ fork σ₄ U (cut (> σ₃) P Q) R
        
    s-fork-r :
        ∀{Δ Θ Θ₁ Θ₂ Θ₃ A B C}        →
        {P : Proc (C ∷ Δ)}           →
        {Q : Proc (A ∷ Θ₁)}          →
        {R : Proc (dual C ∷ Θ₃)}     → 
        (σ  : Γ ≃ Δ  + Θ )           →
        (σ₁ : Θ ≃ Θ₁ + Θ₂)           → 
        (U : Update Θ₂ (A ⊗ B) B Θ₃) →
        let 
            δ  , σ₃ , σ₄ = +-assoc-r σ (+-comm σ₁ )
            δ₁ , σ₅ , U₁ = ≃-update-r σ₃ U
        in
        cut σ P (fork (> σ₁) (next U) Q R) ⊒ fork (+-comm σ₄) U₁ Q (cut σ₅ P R)

    s-refl : 
        ∀{P} → P ⊒ P 
    s-tran : 
        ∀{P Q R} → P ⊒ Q → Q ⊒ R → P ⊒ R
    s-cong :
        ∀{Γ₁ Γ₂ A}                 →
        {P  : Proc (A ∷ Γ₁)}       →
        {Q  : Proc (A ∷ Γ₁)}       →
        {P₁ : Proc (dual A ∷ Γ₂)}  →
        {Q₁ : Proc (dual A ∷ Γ₂)}  →
        (σ : Γ ≃ Γ₁ + Γ₂)          →
        P  ⊒ Q                     → 
        P₁ ⊒ Q₁                    →
        cut  σ P P₁ ⊒ cut σ Q Q₁
