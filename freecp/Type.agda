{-# OPTIONS --rewriting --guardedness #-}
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties as Nat
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂; sym)
open import Relation.Binary.HeterogeneousEquality as Heq using (_≅_; refl)
open import Agda.Builtin.Equality.Rewrite

open import Axioms

data PreType (n r : ℕ) : Set where
  var rav              : Fin n → PreType n r
  skip ⊤ 𝟘 ⊥ 𝟙         : PreType n r
  _⨟_ _&_ _⊕_ _⅋_ _⊗_  : PreType n r → PreType n r → PreType n r
  get put              : ℕ → PreType n r
  inv                  : Fin r → PreType n r
  rec                  : PreType n (suc r) → PreType n r

dual : ∀{n r} → PreType n r → PreType n r
dual (var x) = rav x
dual (rav x) = var x
dual ⊤       = 𝟘
dual 𝟘       = ⊤
dual ⊥       = 𝟙
dual 𝟙       = ⊥
dual (A & B) = dual A ⊕ dual B
dual (A ⊕ B) = dual A & dual B
dual (A ⅋ B) = dual A ⊗ dual B
dual (A ⊗ B) = dual A ⅋ dual B
dual skip    = skip
dual (A ⨟ B) = dual A ⨟ dual B
dual (get μ) = put μ
dual (put μ) = get μ
dual (inv x) = inv x
dual (rec A) = rec (dual A)

dual-inv : ∀{n r} {A : PreType n r} → dual (dual A) ≡ A
dual-inv {_} {_} {var x} = refl
dual-inv {_} {_} {rav x} = refl
dual-inv {_} {_} {skip} = refl
dual-inv {_} {_} {⊤} = refl
dual-inv {_} {_} {𝟘} = refl
dual-inv {_} {_} {⊥} = refl
dual-inv {_} {_} {𝟙} = refl
dual-inv {_} {_} {A ⨟ B} = cong₂ _⨟_ dual-inv dual-inv
dual-inv {_} {_} {A & B} = cong₂ _&_ dual-inv dual-inv
dual-inv {_} {_} {A ⊕ B} = cong₂ _⊕_ dual-inv dual-inv
dual-inv {_} {_} {A ⅋ B} = cong₂ _⅋_ dual-inv dual-inv
dual-inv {_} {_} {A ⊗ B} = cong₂ _⊗_ dual-inv dual-inv
dual-inv {_} {_} {get μ} = refl
dual-inv {_} {_} {put μ} = refl
dual-inv {_} {_} {inv x} = refl
dual-inv {_} {_} {rec A} = cong rec dual-inv

{-# REWRITE dual-inv #-}

-- RECURSIVE TYPES

Renaming : ℕ → ℕ → Set
Renaming r s = Fin r → Fin s

ext : ∀{m n} → Renaming m n → Renaming (suc m) (suc n)
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

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

exts : ∀{n r s} → (Fin r → PreType n s) → Fin (suc r) → PreType n (suc s)
exts σ zero = inv zero
exts σ (suc k) = rename suc (σ k)

dual-exts : ∀{n r s} (σ : Fin r → PreType n s) → exts (dual ∘ σ) ≡ dual ∘ (exts σ)
dual-exts {_} {r} σ = extensionality aux
  where
    aux : (x : Fin (suc r)) → exts (dual ∘ σ) x ≡ dual ((exts σ) x)
    aux zero = refl
    aux (suc x) rewrite dual-rename suc (σ x) = refl

rec-subst : ∀{n r s} → (Fin r → PreType n s) → PreType n r → PreType n s
rec-subst σ (var x) = var x
rec-subst σ (rav x) = rav x
rec-subst σ skip = skip
rec-subst σ ⊤ = ⊤
rec-subst σ 𝟘 = 𝟘
rec-subst σ ⊥ = ⊥
rec-subst σ 𝟙 = 𝟙
rec-subst σ (A ⨟ B) = rec-subst σ A ⨟ rec-subst σ B
rec-subst σ (A & B) = rec-subst σ A & rec-subst σ B
rec-subst σ (A ⊕ B) = rec-subst σ A ⊕ rec-subst σ B
rec-subst σ (A ⅋ B) = rec-subst σ A ⅋ rec-subst σ B
rec-subst σ (A ⊗ B) = rec-subst σ A ⊗ rec-subst σ B
rec-subst σ (get μ) = get μ
rec-subst σ (put μ) = put μ
rec-subst σ (inv x) = σ x
rec-subst σ (rec A) = rec (rec-subst (exts σ) A)

dual-rec-subst : ∀{n r s} (σ : Fin r → PreType n s) (A : PreType n r) →
                 dual (rec-subst σ A) ≡ rec-subst (dual ∘ σ) (dual A)
dual-rec-subst σ (var x) = refl
dual-rec-subst σ (rav x) = refl
dual-rec-subst σ skip = refl
dual-rec-subst σ ⊤ = refl
dual-rec-subst σ 𝟘 = refl
dual-rec-subst σ ⊥ = refl
dual-rec-subst σ 𝟙 = refl
dual-rec-subst σ (A ⨟ B) = cong₂ _⨟_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (A & B) = cong₂ _⊕_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (A ⊕ B) = cong₂ _&_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (A ⅋ B) = cong₂ _⊗_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (A ⊗ B) = cong₂ _⅋_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (get μ) = refl
dual-rec-subst σ (put μ) = refl
dual-rec-subst σ (inv x) = refl
dual-rec-subst σ (rec A) rewrite dual-exts σ = cong rec (dual-rec-subst (exts σ) A)

s-just : ∀{n r} → PreType n r → Fin (suc r) → PreType n r
s-just A zero     = A
s-just A (suc x)  = inv x

dual-s-just : ∀{n r} (A : PreType n r) → dual ∘ s-just A ≡ s-just (dual A)
dual-s-just {_} {r} A = extensionality aux
  where
    aux : (x : Fin (suc r)) → (dual ∘ s-just A) x ≡ s-just (dual A) x
    aux zero = refl
    aux (suc x) = refl

unfold : ∀{n r} → PreType n (suc r) → PreType n r
unfold A = rec-subst (s-just (rec A)) A

dual-unfold : ∀{n r} (A : PreType n (suc r)) → dual (unfold A) ≡ unfold (dual A)
dual-unfold A rewrite dual-rec-subst (s-just (rec A)) A | dual-s-just (rec A) = refl

{-# REWRITE dual-unfold #-}

exts-inv : ∀{n r s} (ρ : Renaming r s) → exts (inv ∘ ρ) ≡ inv ∘ ext ρ
exts-inv {n} {r} ρ = extensionality aux
  where
    aux : (x : Fin (suc r)) → exts (inv ∘ ρ) x ≡ (inv {n} ∘ (ext ρ)) x
    aux zero = refl
    aux (suc x) = refl

rename-as-subst : ∀{n r s} (ρ : Renaming r s) (A : PreType n r) → rename ρ A ≡ rec-subst (inv ∘ ρ) A
rename-as-subst ρ (var x) = refl
rename-as-subst ρ (rav x) = refl
rename-as-subst ρ skip = refl
rename-as-subst ρ ⊤ = refl
rename-as-subst ρ 𝟘 = refl
rename-as-subst ρ ⊥ = refl
rename-as-subst ρ 𝟙 = refl
rename-as-subst ρ (A ⨟ B) = cong₂ _⨟_ (rename-as-subst ρ A) (rename-as-subst ρ B)
rename-as-subst ρ (A & B) = cong₂ _&_ (rename-as-subst ρ A) (rename-as-subst ρ B)
rename-as-subst ρ (A ⊕ B) = cong₂ _⊕_ (rename-as-subst ρ A) (rename-as-subst ρ B)
rename-as-subst ρ (A ⅋ B) = cong₂ _⅋_ (rename-as-subst ρ A) (rename-as-subst ρ B)
rename-as-subst ρ (A ⊗ B) = cong₂ _⊗_ (rename-as-subst ρ A) (rename-as-subst ρ B)
rename-as-subst ρ (get x) = refl
rename-as-subst ρ (put x) = refl
rename-as-subst ρ (inv x) = refl
rename-as-subst ρ (rec A) =
  begin
    rec (rename (ext ρ) A) ≡⟨ cong rec (rename-as-subst (ext ρ) A) ⟩
    rec (rec-subst (inv ∘ ext ρ) A) ≡⟨ cong rec (cong (λ x → rec-subst x A) (sym (exts-inv ρ))) ⟩
    rec (rec-subst (exts (inv ∘ ρ)) A) ∎
  where open Eq.≡-Reasoning

Type : ℕ → Set
Type n = PreType n 0

void : ∀{n} → Type n
void = rec (inv zero)
