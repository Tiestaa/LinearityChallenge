{-# OPTIONS --rewriting --guardedness #-}
module Type.Unfolding where

open import Axioms
open import Function using (_∘_)
open import Data.Nat using (ℕ; suc; zero; _≤_; _<_; s≤s; _⊔_; _+_)
open import Data.Nat.Properties as Nat
open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Fin.Properties as Fin
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; cong; cong₂)

open import Type
open import Type.Renaming

Unfolding : ℕ → ℕ → ℕ → Set
Unfolding n r s = Fin r → PreType n s

exts : ∀{n r s} → Unfolding n r s → Unfolding n (suc r) (suc s)
exts σ zero = inv zero
exts σ (suc k) = rename suc (σ k)

exts∗ : ∀{n r s} → (k : ℕ) → Unfolding n r s → Unfolding n (k + r) (k + s)
exts∗ zero σ = σ
exts∗ (suc k) σ = exts (exts∗ k σ)

dual-exts : ∀{n r s} (σ : Unfolding n r s) → exts (dual ∘ σ) ≡ dual ∘ (exts σ)
dual-exts σ = extensionality aux
  where
    aux : ∀ x → exts (dual ∘ σ) x ≡ dual ((exts σ) x)
    aux zero = refl
    aux (suc x) rewrite dual-rename suc (σ x) = refl

rec-subst : ∀{n r s} → Unfolding n r s → PreType n r → PreType n s
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

dual-rec-subst : ∀{n r s} (σ : Unfolding n r s) (A : PreType n r) →
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

s-just : ∀{n r} → PreType n r → Unfolding n (suc r) r
s-just A zero     = A
s-just A (suc x)  = inv x

dual-s-just : ∀{n r} (A : PreType n r) → dual ∘ s-just A ≡ s-just (dual A)
dual-s-just A = extensionality aux
  where
    aux : ∀ x → (dual ∘ s-just A) x ≡ s-just (dual A) x
    aux zero = refl
    aux (suc x) = refl

unfold : ∀{n r} → PreType n (suc r) → PreType n r
unfold A = rec-subst (s-just (rec A)) A

dual-unfold : ∀{n r} (A : PreType n (suc r)) → dual (unfold A) ≡ unfold (dual A)
dual-unfold A rewrite dual-rec-subst (s-just (rec A)) A | dual-s-just (rec A) = refl

{-# REWRITE dual-unfold #-}

exts-inv : ∀{n r s} (ρ : Renaming r s) → exts (inv ∘ ρ) ≡ inv ∘ ext ρ
exts-inv {n} ρ = extensionality aux
  where
    aux : ∀ x → exts (inv ∘ ρ) x ≡ (inv {n} ∘ (ext ρ)) x
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

IdentityFrom : ∀{n r} → ℕ → Unfolding n (suc r) r → Set
IdentityFrom {_} {r} k σ = (x : Fin (k + r)) → inv x ≡ exts∗ k σ (ext∗ {r} k suc x)

identity-from-suc : ∀{k n r} (σ : Unfolding n (suc r) r) →
                    IdentityFrom k σ → IdentityFrom (suc k) σ
identity-from-suc σ iσ zero = refl
identity-from-suc σ iσ (suc x) rewrite sym (iσ x) = refl

identity-from-s-just : ∀{n r} (A : PreType n r) → IdentityFrom 0 (s-just A)
identity-from-s-just _ _ = refl

useless-rec-subst : ∀{k n r} (σ : Unfolding n (suc r) r) (A : PreType n (k + r)) →
                    IdentityFrom k σ →
                    A ≡ rec-subst (exts∗ k σ) (rename (ext∗ {r} k suc) A)
useless-rec-subst σ (var x) iσ = refl
useless-rec-subst σ (rav x) iσ = refl
useless-rec-subst σ skip iσ = refl
useless-rec-subst σ ⊤ iσ = refl
useless-rec-subst σ 𝟘 iσ = refl
useless-rec-subst σ ⊥ iσ = refl
useless-rec-subst σ 𝟙 iσ = refl
useless-rec-subst σ (A ⨟ B) iσ = cong₂ _⨟_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (A & B) iσ = cong₂ _&_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (A ⊕ B) iσ = cong₂ _⊕_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (A ⅋ B) iσ = cong₂ _⅋_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (A ⊗ B) iσ = cong₂ _⊗_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (get x) iσ = refl
useless-rec-subst σ (put x) iσ = refl
useless-rec-subst σ (inv x) iσ = iσ x
useless-rec-subst σ (rec A) iσ = cong rec (useless-rec-subst σ A (identity-from-suc σ iσ))

rec-subst-s-just : ∀{n r s} (σ : Unfolding n r s) →
                   (A : PreType n (suc r)) (x : Fin (suc r)) →
                   rec-subst σ (s-just (rec A) x) ≡
                   rec-subst (s-just (rec (rec-subst (exts σ) A))) (exts σ x)
rec-subst-s-just σ A zero = refl
rec-subst-s-just σ A (suc x) =
  useless-rec-subst
    ((s-just (rec (rec-subst (exts σ) A))))
    (σ x)
    (identity-from-s-just (rec (rec-subst (exts σ) A)))

exts-suc : ∀{k n r s} (σ : Unfolding n r s) (x : Fin (k + r)) →
           exts (exts∗ k σ) (ext∗ {r} k suc x) ≡ rename (ext∗ {s} k suc) (exts∗ k σ x)
exts-suc {zero} σ x = refl
exts-suc {suc k} σ zero = refl
exts-suc {suc k} {n} {r} {s} σ (suc x) = begin
    exts (exts∗ (suc k) σ) (ext∗ {r} (suc k) suc (suc x))
      ≡⟨⟩
    rename suc (exts (exts∗ k σ) (ext∗ {r} k suc x))
      ≡⟨ cong (rename suc) (exts-suc σ x) ⟩
    rename suc (rename (ext∗ {s} k suc) (exts∗ k σ x))
      ≡⟨ rename-suc-rename {0} (ext∗ {s} k suc) (exts∗ k σ x) ⟩
    rename (ext∗ (suc k) suc) (exts∗ (suc k) σ (suc x)) ∎
  where open Eq.≡-Reasoning

rec-subst-exts-suc : ∀{k n r s} (σ : Unfolding n r s) (A : PreType n (k + r)) →
                     rec-subst (exts (exts∗ k σ)) (rename (ext∗ {r} k suc) A) ≡
                     rename (ext∗ {s} k suc) (rec-subst (exts∗ k σ) A)
rec-subst-exts-suc σ (var x) = refl
rec-subst-exts-suc σ (rav x) = refl
rec-subst-exts-suc σ skip = refl
rec-subst-exts-suc σ ⊤ = refl
rec-subst-exts-suc σ 𝟘 = refl
rec-subst-exts-suc σ ⊥ = refl
rec-subst-exts-suc σ 𝟙 = refl
rec-subst-exts-suc σ (A ⨟ B) = cong₂ _⨟_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (A & B) = cong₂ _&_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (A ⊕ B) = cong₂ _⊕_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (A ⅋ B) = cong₂ _⅋_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (A ⊗ B) = cong₂ _⊗_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (get x) = refl
rec-subst-exts-suc σ (put x) = refl
rec-subst-exts-suc σ (inv x) = exts-suc σ x
rec-subst-exts-suc σ (rec A) = cong rec (rec-subst-exts-suc σ A)

hard-lemma : ∀{k n r s} (σ : Unfolding n r s) →
             (A : PreType n (suc r)) (x : Fin (k + suc r)) →
             rec-subst (exts∗ k σ) (exts∗ k (s-just (rec A)) x) ≡
             rec-subst (exts∗ k (s-just (rec (rec-subst (exts σ) A)))) (exts (exts∗ k σ) x)
hard-lemma {zero} σ A x = rec-subst-s-just σ A x
hard-lemma {suc k} σ A zero = refl
hard-lemma {suc k} {_} {r} σ A (suc x) =
  begin
    rec-subst (exts∗ (suc k) σ) (exts∗ (suc k) (s-just (rec A)) (suc x))
      ≡⟨⟩
    rec-subst (exts (exts∗ k σ)) (exts (exts∗ k (s-just (rec A))) (suc x))
      ≡⟨ rec-subst-exts-suc {0} (exts∗ k σ) (exts∗ k (s-just (rec A)) x) ⟩
    rename suc (rec-subst (exts∗ k σ) (exts∗ k (s-just (rec A)) x))
      ≡⟨ cong (rename suc) (hard-lemma σ A x) ⟩
    rename suc (rec-subst (exts∗ k (s-just (rec (rec-subst (exts σ) A)))) (exts (exts∗ k σ) x))
      ≡⟨ sym (rec-subst-exts-suc {0} (exts∗ k (s-just (rec (rec-subst (exts σ) A)))) (exts (exts∗ k σ) x)) ⟩
    rec-subst (exts (exts∗ k (s-just (rec (rec-subst (exts σ) A))))) (exts (exts (exts∗ k σ)) (suc x))
      ≡⟨⟩
    rec-subst (exts∗ (suc k) (s-just (rec (rec-subst (exts σ) A)))) (exts (exts∗ (suc k) σ) (suc x)) ∎
  where open Eq.≡-Reasoning

rec-subst-rec-subst :
  ∀{k n r s} (σ : Unfolding n r s) →
  (A : PreType n (suc r)) (B : PreType n (suc k + r)) →
  rec-subst (exts∗ k σ) (rec-subst (exts∗ k (s-just (rec A))) B) ≡
  rec-subst (exts∗ k (s-just (rec (rec-subst (exts σ) A)))) (rec-subst (exts∗ (suc k) σ) B)
rec-subst-rec-subst σ C (var x) = refl
rec-subst-rec-subst σ C (rav x) = refl
rec-subst-rec-subst σ C skip = refl
rec-subst-rec-subst σ C ⊤ = refl
rec-subst-rec-subst σ C 𝟘 = refl
rec-subst-rec-subst σ C ⊥ = refl
rec-subst-rec-subst σ C 𝟙 = refl
rec-subst-rec-subst σ C (A ⨟ B) = cong₂ _⨟_ (rec-subst-rec-subst σ C A) (rec-subst-rec-subst σ C B)
rec-subst-rec-subst σ C (A & B) = cong₂ _&_ (rec-subst-rec-subst σ C A) (rec-subst-rec-subst σ C B)
rec-subst-rec-subst σ C (A ⊕ B) = cong₂ _⊕_ (rec-subst-rec-subst σ C A) (rec-subst-rec-subst σ C B)
rec-subst-rec-subst σ C (A ⅋ B) = cong₂ _⅋_ (rec-subst-rec-subst σ C A) (rec-subst-rec-subst σ C B)
rec-subst-rec-subst σ C (A ⊗ B) = cong₂ _⊗_ (rec-subst-rec-subst σ C A) (rec-subst-rec-subst σ C B)
rec-subst-rec-subst σ C (get x) = refl
rec-subst-rec-subst σ C (put x) = refl
rec-subst-rec-subst σ C (inv x) = hard-lemma σ C x
rec-subst-rec-subst σ C (rec B) = cong rec (rec-subst-rec-subst σ C B)

rec-subst-unfold : ∀{n r s} (σ : Unfolding n r s) (A : PreType n (suc r)) →
                   rec-subst σ (unfold A) ≡ unfold (rec-subst (exts σ) A)
rec-subst-unfold σ A = rec-subst-rec-subst σ A A
