{-# OPTIONS --rewriting #-}
open import Data.List.Base using (List; _∷_; []; [_]; _++_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Unary 
open import Data.Nat

open import Type

Context : Set
Context = List Type

infix  4 _≃_+_

data Update (A : Type) (Δ : Context) : Context → Context → Set where
    here : ∀{Γ} → Update A Δ (A ∷ Γ) (Δ ++ Γ)
    next : ∀{Γ Θ C} → Update A Δ Γ Θ → Update A Δ (C ∷ Γ) (C ∷ Θ)

data _≃_+_ : Context → Context → Context → Set where
    • : [] ≃ [] + []  
    <_ : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ A ∷ Δ + Θ
    >_ : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ Δ + A ∷ Θ

+-comm : ∀{Γ Δ Θ} → Γ ≃ Δ + Θ → Γ ≃ Θ + Δ 
+-comm •     = •
+-comm (< p) = > (+-comm p)
+-comm (> p) = < (+-comm p)

+-assoc-l : ∀{Γ Δ Θ Δ` Θ`} → Γ ≃ Δ + Θ → Δ ≃ Δ` + Θ` → ∃[ Γ` ] Γ` ≃ Θ` + Θ × Γ ≃ Δ` + Γ`
+-assoc-l • •     = [] , • , •
+-assoc-l (< p) (< q) with +-assoc-l p q
... | _ , p` , q` = _ , p` , (< q`)
+-assoc-l (< p) (> q) with +-assoc-l p q
... | _ , p` , q` = _ , (< p`) , (> q`)
+-assoc-l (> p) q with +-assoc-l p q 
... | _ , p` , q` = _ , (> p`) , (> q`)

+-assoc-r : ∀{Γ Δ Θ Δ` Θ`} → Γ ≃ Δ + Θ → Θ ≃ Δ` + Θ` → ∃[ Γ` ] Γ` ≃ Δ + Δ`  × Γ ≃ Γ` + Θ`
+-assoc-r p q with +-assoc-l (+-comm p) (+-comm q) 
... | _ , p` , q` = _ , +-comm p` , +-comm q`

++-≃-l : ∀ (Π : Context) {Γ Δ Θ} → Γ ≃ Δ + Θ → (Π ++ Γ) ≃ (Π ++ Δ) + Θ
++-≃-l []      σ = σ
++-≃-l (x ∷ Π) σ = < (++-≃-l Π σ)

≃-update-l : ∀{Γ Δ Θ Δ` A Π} → Γ ≃ Δ + Θ → Update A Π Δ Δ` → ∃[ Γ` ] Γ` ≃ Δ` + Θ × Update A Π Γ Γ`
≃-update-l (< σ) here = _ , ++-≃-l _ σ , here
≃-update-l (< σ) (next U) with ≃-update-l σ U
... | _ , σ` , U` = _ , (< σ`) , next U`
≃-update-l (> σ) here with ≃-update-l σ here
... | _ , σ` , U = _ , (> σ`) , next U
≃-update-l (> σ) (next U) with ≃-update-l σ (next U)
... | _ , σ` , U` = _ , (> σ`) , next U`

≃-update-r : ∀{Γ Δ Θ Θ` A Π} → Γ ≃ Δ + Θ → Update A Π Θ Θ` → ∃[ Γ` ] Γ` ≃ Δ + Θ` × Update A Π Γ Γ`
≃-update-r σ U with ≃-update-l (+-comm σ) U
... | _ , σ` , U`  = _ , +-comm σ` , U`