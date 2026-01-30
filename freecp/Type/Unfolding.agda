{-# OPTIONS --rewriting --guardedness #-}
module Type.Unfolding where

open import Axioms
open import Data.Nat using (ℕ; suc; zero; _≤_; _<_; s≤s; _⊔_; _+_)
open import Data.Nat.Properties as Nat
open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Fin.Properties as Fin
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; cong; cong₂)

open import Type

ext∗ : ∀{r s} → (k : ℕ) → Renaming r s → Renaming (k + r) (k + s)
ext∗ zero ρ = ρ
ext∗ (suc k) ρ = ext (ext∗ k ρ)

exts∗ : ∀{n r s} → (k : ℕ) → Unfolding n r s → Unfolding n (k + r) (k + s)
exts∗ zero σ = σ
exts∗ (suc k) σ = exts (exts∗ k σ)

-- suc+ : ∀{r} → (k : ℕ) → Renaming (k + r) (suc (k + r))
-- suc+ zero = suc
-- suc+ (suc n) = ext (suc+ n)

-- suc+ext∗ : ∀{r s} {ρ : Renaming r s} (k : ℕ) (x : Fin (k + r)) →
--           suc+ k (ext∗ k ρ x) ≡ ext (ext∗ k ρ) (suc+ k x)
-- suc+ext∗ zero x = refl
-- suc+ext∗ (suc k) zero = refl
-- suc+ext∗ (suc k) (suc x) = cong suc (suc+ext∗ k x)

-- rename-suc-rename : ∀{k n r s} (ρ : Renaming r s) (A : PreType n (k + r)) →
--                     rename (suc+ k) (rename (ext∗ k ρ) A) ≡
--                     rename (ext (ext∗ k ρ)) (rename (suc+ k) A)
-- rename-suc-rename ρ (var x) = refl
-- rename-suc-rename ρ (rav x) = refl
-- rename-suc-rename ρ skip = refl
-- rename-suc-rename ρ ⊤ = refl
-- rename-suc-rename ρ 𝟘 = refl
-- rename-suc-rename ρ ⊥ = refl
-- rename-suc-rename ρ 𝟙 = refl
-- rename-suc-rename ρ (A ⨟ B) = cong₂ _⨟_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
-- rename-suc-rename ρ (A & B) = cong₂ _&_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
-- rename-suc-rename ρ (A ⊕ B) = cong₂ _⊕_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
-- rename-suc-rename ρ (A ⅋ B) = cong₂ _⅋_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
-- rename-suc-rename ρ (A ⊗ B) = cong₂ _⊗_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
-- rename-suc-rename ρ (get x) = refl
-- rename-suc-rename ρ (put x) = refl
-- rename-suc-rename {k} ρ (inv x) = cong inv (suc+ext∗ k x)
-- rename-suc-rename ρ (rec A) = cong rec (rename-suc-rename ρ A)

-- exts-rename : ∀{k n r s} (x : Fin (k + r)) (σ : Unfolding n r s) →
--               exts (exts∗ k σ) (suc+ k x) ≡ rename (suc+ k) (exts∗ k σ x)
-- exts-rename {zero} x σ = refl
-- exts-rename {suc k} zero σ = refl
-- exts-rename {suc k} (suc x) σ = begin
--   rename suc (exts (exts∗ k σ) (suc+ k x))
--     ≡⟨ cong (rename suc) (exts-rename x σ) ⟩
--   rename suc (rename (suc+ k) (exts∗ k σ x))
--     ≡⟨ rename-suc-rename {0} (suc+ k) (exts∗ k σ x) ⟩
--   rename (ext (suc+ k)) (rename suc (exts∗ k σ x))
--   ∎ where open Eq.≡-Reasoning

-- rec-subst-rename : ∀{k n r s} (A : PreType n (k + r)) (σ : Unfolding n r s) →
--                    rec-subst (exts∗ (suc k) σ) (rename (suc+ k) A) ≡
--                    rename (suc+ k) (rec-subst (exts∗ k σ) A)
-- rec-subst-rename (var x) σ = refl
-- rec-subst-rename (rav x) σ = refl
-- rec-subst-rename skip σ = refl
-- rec-subst-rename ⊤ σ = refl
-- rec-subst-rename 𝟘 σ = refl
-- rec-subst-rename ⊥ σ = refl
-- rec-subst-rename 𝟙 σ = refl
-- rec-subst-rename (A ⨟ B) σ = cong₂ _⨟_ (rec-subst-rename A σ) (rec-subst-rename B σ)
-- rec-subst-rename (A & B) σ = cong₂ _&_ (rec-subst-rename A σ) (rec-subst-rename B σ)
-- rec-subst-rename (A ⊕ B) σ = cong₂ _⊕_ (rec-subst-rename A σ) (rec-subst-rename B σ)
-- rec-subst-rename (A ⅋ B) σ = cong₂ _⅋_ (rec-subst-rename A σ) (rec-subst-rename B σ)
-- rec-subst-rename (A ⊗ B) σ = cong₂ _⊗_ (rec-subst-rename A σ) (rec-subst-rename B σ)
-- rec-subst-rename (get x) σ = refl
-- rec-subst-rename (put x) σ = refl
-- rec-subst-rename (inv x) σ = exts-rename x σ
-- rec-subst-rename (rec A) σ = cong rec (rec-subst-rename A σ)

-- rec-subst-exts : ∀{n r s t} (τ : Unfolding n r s) (σ : Unfolding n s t) →
--                  rec-subst (exts σ) ∘ exts τ ≡ exts (rec-subst σ ∘ τ)
-- rec-subst-exts τ σ = extensionality aux
--   where
--     aux : ∀ x → rec-subst (exts σ) (exts τ x) ≡ exts (rec-subst σ ∘ τ) x
--     aux zero = refl
--     aux (suc x) = rec-subst-rename (τ x) σ

{-# REWRITE +-suc #-}

ext∗-suc-ext∗ : ∀{r s} {ρ : Renaming r s} (k : ℕ) (x : Fin (k + r)) →
                ext∗ {s} k suc (ext∗ k ρ x) ≡ ext (ext∗ k ρ) (ext∗ {r} k suc x)
ext∗-suc-ext∗ zero x = refl
ext∗-suc-ext∗ (suc k) zero = refl
ext∗-suc-ext∗ (suc k) (suc x) = cong suc (ext∗-suc-ext∗ k x)

-- rec-subst-compose : ∀{n r s t} (A : PreType n r) {τ : Unfolding n r s} {σ : Unfolding n s t} →
--                     rec-subst σ (rec-subst τ A) ≡ rec-subst (rec-subst σ ∘ τ) A
-- rec-subst-compose (var x) = refl
-- rec-subst-compose (rav x) = refl
-- rec-subst-compose skip = refl
-- rec-subst-compose ⊤ = refl
-- rec-subst-compose 𝟘 = refl
-- rec-subst-compose ⊥ = refl
-- rec-subst-compose 𝟙 = refl
-- rec-subst-compose (A ⨟ B) = cong₂ _⨟_ (rec-subst-compose A) (rec-subst-compose B)
-- rec-subst-compose (A & B) = cong₂ _&_ (rec-subst-compose A) (rec-subst-compose B)
-- rec-subst-compose (A ⊕ B) = cong₂ _⊕_ (rec-subst-compose A) (rec-subst-compose B)
-- rec-subst-compose (A ⅋ B) = cong₂ _⅋_ (rec-subst-compose A) (rec-subst-compose B)
-- rec-subst-compose (A ⊗ B) = cong₂ _⊗_ (rec-subst-compose A) (rec-subst-compose B)
-- rec-subst-compose (get x) = refl
-- rec-subst-compose (put x) = refl
-- rec-subst-compose (inv x) = refl
-- rec-subst-compose (rec A) {τ} {σ} = begin
--   rec (rec-subst (exts σ) (rec-subst (exts τ) A)) ≡⟨ cong rec (rec-subst-compose A) ⟩
--   rec (rec-subst (rec-subst (exts σ) ∘ exts τ) A) ≡⟨ cong (λ x → rec (rec-subst x A)) (rec-subst-exts τ σ) ⟩
--   rec (rec-subst (exts (rec-subst σ ∘ τ)) A) ∎
--   where open Eq.≡-Reasoning

-- exts-exts∗ : ∀{n r s} (k : ℕ) (σ : Unfolding n r s) → exts (exts∗ k σ) ≡ exts∗ k (exts σ)
-- exts-exts∗ zero σ = refl
-- exts-exts∗ (suc k) σ = cong exts (exts-exts∗ k σ)

-- rec-subst-exts∗ : ∀{k n r s t} (τ : Unfolding n r s) (σ : Unfolding n s t) →
--                   (x : Fin (k + r)) → rec-subst (exts∗ k σ) (exts∗ k τ x) ≡ exts∗ k (rec-subst σ ∘ τ) x
-- rec-subst-exts∗ {zero} τ σ x = refl
-- rec-subst-exts∗ {suc k} τ σ x = begin
--   rec-subst (exts (exts∗ k σ)) (exts (exts∗ k τ) x)
--     ≡⟨ cong₂ (λ u v → rec-subst u (v x)) (exts-exts∗ k σ) (exts-exts∗ k τ) ⟩
--   rec-subst (exts∗ k (exts σ)) (exts∗ k (exts τ) x)
--     ≡⟨ rec-subst-exts∗ (exts τ) (exts σ) x ⟩
--   exts∗ k (rec-subst (exts σ) ∘ (exts τ)) x
--     ≡⟨ cong (λ u → exts∗ k u x) (rec-subst-exts τ σ) ⟩
--   exts∗ k (exts (rec-subst σ ∘ τ)) x
--     ≡⟨ cong (λ u → u x) (sym (exts-exts∗ k (rec-subst σ ∘ τ))) ⟩
--   exts (exts∗ k (rec-subst σ ∘ τ)) x ∎
--   where open Eq.≡-Reasoning

-- easy : ∀{k n r s t} (A : PreType n (k + r)) (τ : Unfolding n r s) (σ : Unfolding n s t) →
--        rec-subst (exts∗ k σ) (rec-subst (exts∗ k τ) A) ≡
--        rec-subst (exts∗ k (rec-subst σ ∘ τ)) A
-- easy (var x) τ σ = refl
-- easy (rav x) τ σ = refl
-- easy skip τ σ = refl
-- easy ⊤ τ σ = refl
-- easy 𝟘 τ σ = refl
-- easy ⊥ τ σ = refl
-- easy 𝟙 τ σ = refl
-- easy (A ⨟ B) τ σ = cong₂ _⨟_ (easy A τ σ) (easy B τ σ)
-- easy (A & B) τ σ = cong₂ _&_ (easy A τ σ) (easy B τ σ)
-- easy (A ⊕ B) τ σ = cong₂ _⊕_ (easy A τ σ) (easy B τ σ)
-- easy (A ⅋ B) τ σ = cong₂ _⅋_ (easy A τ σ) (easy B τ σ)
-- easy (A ⊗ B) τ σ = cong₂ _⊗_ (easy A τ σ) (easy B τ σ)
-- easy (get x) τ σ = refl
-- easy (put x) τ σ = refl
-- easy (inv x) τ σ = rec-subst-exts∗ τ σ x
-- easy (rec A) τ σ = cong rec (easy A τ σ)

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

rename-suc-rename' : ∀{k n r s} (ρ : Renaming r s) (A : PreType n (k + r)) →
                     rename (ext∗ {s} k suc) (rename (ext∗ k ρ) A) ≡
                     rename (ext (ext∗ k ρ)) (rename (ext∗ {r} k suc) A)
rename-suc-rename' ρ (var x) = refl
rename-suc-rename' ρ (rav x) = refl
rename-suc-rename' ρ skip = refl
rename-suc-rename' ρ ⊤ = refl
rename-suc-rename' ρ 𝟘 = refl
rename-suc-rename' ρ ⊥ = refl
rename-suc-rename' ρ 𝟙 = refl
rename-suc-rename' ρ (A ⨟ B) = cong₂ _⨟_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (A & B) = cong₂ _&_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (A ⊕ B) = cong₂ _⊕_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (A ⅋ B) = cong₂ _⅋_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (A ⊗ B) = cong₂ _⊗_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (get x) = refl
rename-suc-rename' ρ (put x) = refl
rename-suc-rename' {k} ρ (inv x) = cong inv (ext∗-suc-ext∗ k x)
rename-suc-rename' ρ (rec A) = cong rec (rename-suc-rename' ρ A)

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
      ≡⟨ rename-suc-rename' {0} (ext∗ {s} k suc) (exts∗ k σ x) ⟩
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
