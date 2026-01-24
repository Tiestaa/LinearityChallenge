{-# OPTIONS --rewriting --guardedness #-}
open import Function using (_∘_)
open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_]; _++_; map)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Type
open import Type.Equivalence

Context : ℕ → Set
Context n = List (Type n)

infix  4 _≃_+_
infixr 8 _─∗_
infixr 9 _∗_

data _≃_+_ {n} : Context n → Context n → Context n → Set where
  •   : [] ≃ [] + []
  <_  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ A ∷ Δ + Θ
  >_  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ Δ + A ∷ Θ

+-comm : ∀{n} {Γ Δ Θ : Context n} → Γ ≃ Δ + Θ → Γ ≃ Θ + Δ
+-comm • = •
+-comm (< p) = > (+-comm p)
+-comm (> p) = < (+-comm p)

++≃+ : ∀{n} {Γ Δ : Context n} → Γ ++ Δ ≃ Γ + Δ
++≃+ {_} {[]}    {[]}    = •
++≃+ {_} {[]}    {_ ∷ _} = > ++≃+
++≃+ {_} {_ ∷ _} {_}     = < ++≃+

≫ : ∀{n} {Γ : Context n} → Γ ≃ [] + Γ
≫ = ++≃+ {_} {[]}

≪ : ∀{n} {Γ : Context n} → Γ ≃ Γ + []
≪ = +-comm ≫

+-assoc-r  : ∀{n} {Γ Δ Θ Δ′ Θ′ : Context n} → Γ ≃ Δ + Θ → Θ ≃ Δ′ + Θ′ →
             ∃[ Γ′ ] Γ′ ≃ Δ + Δ′ × Γ ≃ Γ′ + Θ′
+-assoc-r • • = [] , • , •
+-assoc-r (< p) q with +-assoc-r p q
... | _ , p′ , q′ = _ , < p′ , < q′
+-assoc-r (> p) (< q) with +-assoc-r p q
... | _ , p′ , q′ = _ , > p′ , < q′
+-assoc-r (> p) (> q) with +-assoc-r p q
... | _ , p′ , q′ = _ , p′ , > q′

+-assoc-l  : ∀{n} {Γ Δ Θ Δ′ Θ′ : Context n} → Γ ≃ Δ + Θ → Δ ≃ Δ′ + Θ′ →
             ∃[ Γ′ ] Γ′ ≃ Θ′ + Θ × Γ ≃ Δ′ + Γ′
+-assoc-l p q with +-assoc-r (+-comm p) (+-comm q)
... | Δ , r , p′ = Δ , +-comm r , +-comm p′

+-empty-l : ∀{n} {Γ Δ : Context n} → Γ ≃ [] + Δ → Γ ≡ Δ
+-empty-l • = refl
+-empty-l (> p) = cong (_ ∷_) (+-empty-l p)

data _∗_ {n} (P Q : Pred (Context n) _) (Γ : Context n) : Set where
  _⟨_⟩_ : ∀{Δ Θ} → P Δ → Γ ≃ Δ + Θ → Q Θ → (P ∗ Q) Γ

∗-comm : ∀{n} {P Q : Pred (Context n) _} → ∀[ P ∗ Q ⇒ Q ∗ P ]
∗-comm (p ⟨ σ ⟩ q) = q ⟨ +-comm σ ⟩ p

∗-assoc-l : ∀{n} {P Q R : Pred (Context n) _} → ∀[ (P ∗ Q) ∗ R ⇒ P ∗ (Q ∗ R) ]
∗-assoc-l ((p ⟨ σ ⟩ q) ⟨ ρ ⟩ r) with +-assoc-l ρ σ
... | _ , σ' , ρ' = p ⟨ ρ' ⟩ (q ⟨ σ' ⟩ r)

_─∗_ : ∀{n} → Pred (Context n) _ → Pred (Context n) _ → Context n → Set
(P ─∗ Q) Δ = ∀{Θ Γ} → Γ ≃ Δ + Θ → P Θ → Q Γ

curry∗ : ∀{n} {P Q R : Pred (Context n) _} → ∀[ P ∗ Q ⇒ R ] → ∀[ P ⇒ Q ─∗ R ]
curry∗ F px σ qx = F (px ⟨ σ ⟩ qx)

substc : ∀{m n} → (∀{s} → Fin m → PreType n s) → Context m → Context n
substc σ = map (subst σ)

substc-compose : ∀{m n o} (σ₁ : Substitution m n) (σ₂ : Substitution n o)
                 (Γ : Context m) → substc σ₂ (substc σ₁ Γ) ≡ substc (subst σ₂ ∘ σ₁) Γ
substc-compose σ₁ σ₂ [] = refl
substc-compose σ₁ σ₂ (A ∷ Γ) = cong₂ _∷_ (subst-compose σ₁ σ₂ A) (substc-compose σ₁ σ₂ Γ)

+-subst : ∀{m n}{Γ Δ Θ : Context m} (σ : ∀{s} → Fin m → PreType n s) → Γ ≃ Δ + Θ → substc σ Γ ≃ substc σ Δ + substc σ Θ
+-subst σ • = •
+-subst σ (< p) = < +-subst σ p
+-subst σ (> p) = > +-subst σ p

data _≈c_ {n} : Context n → Context n → Set where
  [] : [] ≈c []
  _∷_ : ∀{A B Γ Δ} → A ≈ B → Γ ≈c Δ → (A ∷ Γ) ≈c (B ∷ Δ)

≈c-refl : ∀{n} {Γ : Context n} → Γ ≈c Γ
≈c-refl {_} {[]} = []
≈c-refl {_} {A ∷ Γ} = ≈refl ∷ ≈c-refl

+≈ : ∀{n} {Γ Δ Δ' Θ : Context n} → Γ ≃ Δ + Θ → Δ ≈c Δ' → ∃[ Γ' ] Γ' ≃ Δ' + Θ × Γ ≈c Γ'
+≈ • [] = _ , • , []
+≈ (< p) (x ∷ eq) with +≈ p eq
... | Γ' , p' , eq' = _ , < p' , x ∷ eq'
+≈ (> p) eq with +≈ p eq
... | Γ' , p' , eq' = _ , > p' , ≈refl ∷ eq'
