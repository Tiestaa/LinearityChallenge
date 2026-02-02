{-# OPTIONS --rewriting --guardedness #-}
module Type.Renaming where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_)
open import Data.Nat.Properties as Nat
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂; sym)
open import Relation.Binary.HeterogeneousEquality as Heq using (_≅_; refl)
open import Agda.Builtin.Equality.Rewrite

open import Type.Base

Renaming : ℕ → ℕ → Set
Renaming r s = Fin r → Fin s

ext : ∀{m n} → Renaming m n → Renaming (suc m) (suc n)
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

ext∗ : ∀{r s} → (k : ℕ) → Renaming r s → Renaming (k + r) (k + s)
ext∗ zero ρ = ρ
ext∗ (suc k) ρ = ext (ext∗ k ρ)

rename : ∀{n r s} → Renaming r s → PreType n r → PreType n s
rename ρ (var x) = var x
rename ρ (rav x) = rav x
rename ρ skip = skip
rename ρ ⊤    = ⊤
rename ρ 𝟘    = 𝟘
rename ρ ⊥ = ⊥
rename ρ 𝟙 = 𝟙
rename ρ (A ⨟ B) = rename ρ A ⨟ rename ρ B
rename ρ (A & B) = rename ρ A & rename ρ B
rename ρ (A ⊕ B) = rename ρ A ⊕ rename ρ B
rename ρ (A ⅋ B) = rename ρ A ⅋ rename ρ B
rename ρ (A ⊗ B) = rename ρ A ⊗ rename ρ B
rename ρ (get μ) = get μ
rename ρ (put μ) = put μ
rename ρ (inv x) = inv (ρ x)
rename ρ (rec A) = rec (rename (ext ρ) A)

dual-rename : ∀{n r s} (ρ : Renaming r s) (A : PreType n r) → dual (rename ρ A) ≡ rename ρ (dual A)
dual-rename ρ (var x) = refl
dual-rename ρ (rav x) = refl
dual-rename ρ skip = refl
dual-rename ρ ⊤ = refl
dual-rename ρ 𝟘 = refl
dual-rename ρ ⊥ = refl
dual-rename ρ 𝟙 = refl
dual-rename ρ (A ⨟ B) = cong₂ _⨟_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (A & B) = cong₂ _⊕_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (A ⊕ B) = cong₂ _&_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (A ⅋ B) = cong₂ _⊗_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (A ⊗ B) = cong₂ _⅋_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (get μ) = refl
dual-rename ρ (put μ) = refl
dual-rename ρ (inv x) = refl
dual-rename ρ (rec A) = cong rec (dual-rename (ext ρ) A)

{-# REWRITE +-suc #-}

ext∗-suc-ext∗ : ∀{r s} {ρ : Renaming r s} (k : ℕ) (x : Fin (k + r)) →
                ext∗ {s} k suc (ext∗ k ρ x) ≡ ext (ext∗ k ρ) (ext∗ {r} k suc x)
ext∗-suc-ext∗ zero x = refl
ext∗-suc-ext∗ (suc k) zero = refl
ext∗-suc-ext∗ (suc k) (suc x) = cong suc (ext∗-suc-ext∗ k x)

rename-suc-rename : ∀{k n r s} (ρ : Renaming r s) (A : PreType n (k + r)) →
                     rename (ext∗ {s} k suc) (rename (ext∗ k ρ) A) ≡
                     rename (ext (ext∗ k ρ)) (rename (ext∗ {r} k suc) A)
rename-suc-rename ρ (var x) = refl
rename-suc-rename ρ (rav x) = refl
rename-suc-rename ρ skip = refl
rename-suc-rename ρ ⊤ = refl
rename-suc-rename ρ 𝟘 = refl
rename-suc-rename ρ ⊥ = refl
rename-suc-rename ρ 𝟙 = refl
rename-suc-rename ρ (A ⨟ B) = cong₂ _⨟_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (A & B) = cong₂ _&_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (A ⊕ B) = cong₂ _⊕_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (A ⅋ B) = cong₂ _⅋_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (A ⊗ B) = cong₂ _⊗_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (get x) = refl
rename-suc-rename ρ (put x) = refl
rename-suc-rename {k} ρ (inv x) = cong inv (ext∗-suc-ext∗ k x)
rename-suc-rename ρ (rec A) = cong rec (rename-suc-rename ρ A)
