{-# OPTIONS --rewriting --guardedness #-}
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_)
import Data.Nat.Properties as Nat
open import Data.List.Base using ([]; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Type
open import Type.Transitions
open import Type.Substitution
open import Type.Equivalence
open import Context
open import Permutations
open import Process
open import Congruence

data _⊢_↝_ {n Σ Γ} (ℙ : Def Σ) : ∀{Δ μ ν} → Proc {n} Σ μ Γ → Proc Σ ν Δ → Set where
  r-call      : ∀{T} (x : T ∈ Σ) (σ : Substitution (T .ProcType.n) n) →
                (π : substc σ (T .ProcType.context) ↭ Γ) →
                ℙ ⊢ call x σ π ↝ ↭proc π (substp σ (ℙ x))
  r-link      : ∀{Δ A B C μ ν} {P : Proc Σ ν (B ∷ Δ)} (eq : dual A ≈ B) (eq' : dual A ≈ C) (p : Γ ≃ [ C ] + Δ) →
                let _ , p' , eq'' = +≈ p (≈trans (≈sym eq') eq ∷ []) in
                ℙ ⊢ cut {A = A} {B} eq (link {μ = μ} eq' (ch ⟨ < > • ⟩ ch) ⟨ p ⟩ P) ↝
                ↭proc (↭concat p') P
  r-close     : ∀{μ ν} {P : Proc Σ μ Γ} (eq : 𝟙 ≈ 𝟙) (p : Γ ≃ Γ + []) (p₀ : Γ ≃ [] + Γ) →
                ℙ ⊢ cut eq (wait (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ close {μ = ν} ch) ↝ P
  r-select-l  : ∀{Γ₁ Γ₂ A B A' B' μ ν} {P : Proc Σ μ (A ∷ Γ₁)} {Q : Proc Σ μ (B ∷ Γ₁)} {R : Proc Σ ν (A' ∷ Γ₂)}
                (eq : (dual A ⊕ dual B) ≈ (A' ⊕ B'))
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                ℙ ⊢ cut eq (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩ select (ch ⟨ < q₀ ⟩ inj₁ R)) ↝
                    cut (≈after ⊕L ⊕L eq) (P ⟨ p ⟩ R)
  r-select-r  : ∀{Γ₁ Γ₂ A B A' B' μ ν} {P : Proc Σ μ (A ∷ Γ₁)} {Q : Proc Σ μ (B ∷ Γ₁)} {R : Proc Σ ν (B' ∷ Γ₂)}
                (eq : (dual A ⊕ dual B) ≈ (A' ⊕ B'))
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                ℙ ⊢ cut eq (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩ select (ch ⟨ < q₀ ⟩ inj₂ R)) ↝
                    cut (≈after ⊕R ⊕R eq) (Q ⟨ p ⟩ R)
  r-fork      : ∀{Γ₁ Γ₂ Γ₃ Δ A B A' B' μ ν ω} {P : Proc Σ μ (A ∷ B ∷ Γ₁)} {Q : Proc Σ ν (A' ∷ Γ₂)} {R : Proc Σ ω (B' ∷ Γ₃)}
                (eq : (dual A ⊗ dual B) ≈ (A' ⊗ B'))
                (p : Γ ≃ Γ₁ + Δ) (p₀ : Γ₁ ≃ [] + Γ₁) (q : Δ ≃ Γ₂ + Γ₃) (q₀ : Δ ≃ [] + Δ) →
                let _ , p' , q' = +-assoc-r p q in
                ℙ ⊢ cut eq (join (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ fork (ch ⟨ < q₀ ⟩ (Q ⟨ q ⟩ R))) ↝
                    cut (≈after ⊗R ⊗R eq) (cut (≈after ⊗L ⊗L eq) (P ⟨ < p' ⟩ Q) ⟨ q' ⟩ R)
  r-put        : ∀{Γ₁ Γ₂ A A' μ₁ μ₂ ν ω} {P : Proc Σ μ₁ (A ∷ Γ₁)} {Q : Proc Σ μ₂ (A' ∷ Γ₂)}
                (eq : (put ω ⨟ dual A) ≈ (put ω ⨟ A')) (eq' : μ₁ ≡ ν + ω)
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                ℙ ⊢ cut eq (get eq' (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ put (ch ⟨ (< q₀) ⟩ Q)) ↝
                cut (≈trans A≈skip⨟A (≈trans (≈after (seq put λ ()) (seq put λ ()) eq) (≈sym A≈skip⨟A))) (P ⟨ p ⟩ Q)
  r-cut        : ∀{Γ₁ Γ₂ A B A' Γ₁' μ ν ω} {P : Proc Σ μ (A ∷ Γ₁)} {R : Proc Σ ν (B ∷ Γ₂)} {Q : Proc Σ ω (A' ∷ Γ₁')}
                 (eq : dual A ≈ B) (eqA : A ≈ A') (eqC : Γ₁ ≈c Γ₁') (p : Γ ≃ Γ₁ + Γ₂) →
                 ℙ ⊢ P ↝ Q →
                 let _ , p' , eq'' = +≈ p eqC in
                 ℙ ⊢ cut eq (P ⟨ p ⟩ R) ↝ cut (≈trans (≈dual (≈sym eqA)) eq) (Q ⟨ p' ⟩ R)
  r-cong       : ∀{Δ μ ν ω} {P : Proc {n} Σ μ Γ} {R : Proc Σ ν Γ} {Q : Proc Σ ω Δ} →
                 P ⊒ R → ℙ ⊢ R ↝ Q → ℙ ⊢ P ↝ Q

↝≈ : ∀{n Σ Γ Δ μ ν}{P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Δ} {ℙ : Def Σ} → ℙ ⊢ P ↝ Q → Γ ≈c Δ
↝≈ (r-call x σ π) = ≈c-refl
↝≈ (r-link eq eq' p) with +≈ p (≈trans (≈sym eq') eq ∷ [])
... | _ , _ , eq'' = eq''
↝≈ (r-close eq p p₀) = ≈c-refl
↝≈ (r-select-l eq p p₀ q₀) = ≈c-refl
↝≈ (r-select-r eq p p₀ q₀) = ≈c-refl
↝≈ (r-fork eq p p₀ q q₀) = ≈c-refl
↝≈ (r-put eq eq' p p₀ q₀) = ≈c-refl
↝≈ (r-cut eq eqA eqC p red ) with +≈ p eqC
... | _ , _ , eq' = eq'
↝≈ (r-cong _ red) = ↝≈ red

↝size : ∀{n Σ Γ Δ μ ν}{P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Δ} {ℙ : Def Σ} → ℙ ⊢ P ↝ Q → ν < μ
↝size (r-call x σ π) = Nat.≤-refl
↝size (r-link {μ = μ} {ν} eq eq' p) rewrite Nat.+-comm μ ν = Nat.m≤m+n (suc ν) μ
↝size (r-close {μ = μ} {ν} eq p p₀) rewrite Nat.+-suc μ ν = Nat.m≤m+n (suc μ) ν
↝size (r-select-l {μ = μ} eq p p₀ q₀) = Nat.+-monoʳ-< μ Nat.≤-refl
↝size (r-select-r {μ = μ} eq p p₀ q₀) = Nat.+-monoʳ-< μ Nat.≤-refl
↝size (r-fork {μ = μ} {ν} {ω} eq p p₀ q q₀)
  rewrite Nat.+-assoc μ ν ω | Nat.+-suc μ (ν + ω) = Nat.≤-refl
↝size (r-put {μ₂ = μ₂} {ν} {ω} eq refl p p₀ q₀)
  rewrite Nat.+-assoc ν ω μ₂ | Nat.+-suc ν (μ₂ + ω) | Nat.+-comm ω μ₂ = Nat.≤-refl
↝size (r-cut {ν = ν} eq eqA eqC p red) = Nat.+-monoˡ-< ν (↝size red)
↝size (r-cong pc red) with ⊒size pc
... | refl = ↝size red

data _⊢_↝*_ {n Σ Γ} (ℙ : Def Σ) : ∀{Δ μ ν} → Proc {n} Σ μ Γ → Proc {n} Σ ν Δ → Set where
  refl  : ∀{μ} {P : Proc Σ μ Γ} → ℙ ⊢ P ↝* P
  trans : ∀{μ ν ω Δ Θ} {P : Proc Σ μ Γ} {Q : Proc Σ ν Δ} {R : Proc Σ ω Θ} →
          ℙ ⊢ P ↝ Q → ℙ ⊢ Q ↝* R → ℙ ⊢ P ↝* R

run-length : ∀{n Σ μ ν Γ Δ} (ℙ : Def Σ) {P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Δ} ->
             ℙ ⊢ P ↝* Q -> ℕ
run-length _ refl = 0
run-length ℙ (trans _ reds) = suc (run-length ℙ reds)
