{-# OPTIONS --rewriting --guardedness #-}
module Type.Substitutions where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties as Nat
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties as Fin
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂; sym)
open import Relation.Binary.HeterogeneousEquality as Heq using (_≅_; refl)
open import Agda.Builtin.Equality.Rewrite

open import Axioms
open import Type
open import Type.Equality

record Substitution (m n : ℕ) : Set where
  field
    at : ∀{u} → Fin m → PreType n u
    -- a substitution must be COHERENT, namely it must be
    -- independent of the index denoting the number of recursion
    -- variables
    co : ∀{u v} (x : Fin m) → at {u} x == at {v} x

open Substitution public

skip-subst : ∀{m n} → Substitution m n
skip-subst .at _ = skip
skip-subst .co _ = skip

subst : ∀{n m r} → Substitution n m → PreType n r → PreType m r
subst σ (var x) = σ .at x
subst σ (rav x) = dual (σ .at x)
subst σ skip = skip
subst σ ⊤ = ⊤
subst σ 𝟘 = 𝟘
subst σ ⊥ = ⊥
subst σ 𝟙 = 𝟙
subst σ (A ⨟ B) = subst σ A ⨟ subst σ B
subst σ (A & B) = subst σ A & subst σ B
subst σ (A ⊕ B) = subst σ A ⊕ subst σ B
subst σ (A ⅋ B) = subst σ A ⅋ subst σ B
subst σ (A ⊗ B) = subst σ A ⊗ subst σ B
subst σ (get μ) = get μ
subst σ (put μ) = put μ
subst σ (inv x) = inv x
subst σ (rec A) = rec (subst σ A)

Coherent : ∀{m n} → (∀{u} → PreType m u → PreType n u) → Set
Coherent {m} f = ∀{r s} {A : PreType m r} {B : PreType m s} -> A == B → f A == f B

dual-coherent : ∀{n} → Coherent {n} dual
dual-coherent skip = skip
dual-coherent bot = one
dual-coherent one = bot
dual-coherent top = zero
dual-coherent zero = top
dual-coherent put = get
dual-coherent get = put
dual-coherent var = rav
dual-coherent rav = var
dual-coherent (seq x y) = seq (dual-coherent x) (dual-coherent y)
dual-coherent (par x y) = ten (dual-coherent x) (dual-coherent y)
dual-coherent (ten x y) = par (dual-coherent x) (dual-coherent y)
dual-coherent (amp x y) = plus (dual-coherent x) (dual-coherent y)
dual-coherent (plus x y) = amp (dual-coherent x) (dual-coherent y)
dual-coherent (inv x) = inv x
dual-coherent (rec x) = rec (dual-coherent x)

subst-coherent : ∀{m n} (σ : Substitution m n) → Coherent (subst σ)
subst-coherent σ skip = skip
subst-coherent σ bot = bot
subst-coherent σ one = one
subst-coherent σ top = top
subst-coherent σ zero = zero
subst-coherent σ put = put
subst-coherent σ get = get
subst-coherent σ var = σ .co _
subst-coherent σ rav = dual-coherent (σ .co _)
subst-coherent σ (seq x y) = seq (subst-coherent σ x) (subst-coherent σ y)
subst-coherent σ (par x y) = par (subst-coherent σ x) (subst-coherent σ y)
subst-coherent σ (ten x y) = ten (subst-coherent σ x) (subst-coherent σ y)
subst-coherent σ (amp x y) = amp (subst-coherent σ x) (subst-coherent σ y)
subst-coherent σ (plus x y) = plus (subst-coherent σ x) (subst-coherent σ y)
subst-coherent σ (inv x) = inv x
subst-coherent σ (rec x) = rec (subst-coherent σ x)

_·_ : ∀{m n o} → Substitution n o → Substitution m n → Substitution m o
(τ · σ) .at = subst τ ∘ σ .at
(τ · σ) .co = subst-coherent τ ∘ σ .co

Dual : ∀{m n} → Substitution m n → Substitution m n
Dual σ .at = dual ∘ σ .at
Dual σ .co x = dual-coherent (σ .co x)

dual-subst : ∀{n m r} (σ : Substitution n m) (A : PreType n r) →
             dual (subst σ A) ≡ subst σ (dual A)
dual-subst σ (var x) = refl
dual-subst σ (rav x) = refl
dual-subst σ skip = refl
dual-subst σ ⊤ = refl
dual-subst σ 𝟘 = refl
dual-subst σ ⊥ = refl
dual-subst σ 𝟙 = refl
dual-subst σ (A ⨟ B) = cong₂ _⨟_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (A & B) = cong₂ _⊕_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (A ⊕ B) = cong₂ _&_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (A ⅋ B) = cong₂ _⊗_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (A ⊗ B) = cong₂ _⅋_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (get μ) = refl
dual-subst σ (put μ) = refl
dual-subst σ (inv x) = refl
dual-subst σ (rec A) = cong rec (dual-subst σ A)

subst-compose : ∀{m n o r} (σ₁ : Substitution m n) (σ₂ : Substitution n o) →
                (A : PreType m r) → subst σ₂ (subst σ₁ A) ≡ subst (σ₂ · σ₁) A
subst-compose σ₁ σ₂ (var x) = refl
subst-compose σ₁ σ₂ (rav x) = sym (dual-subst σ₂ (σ₁ .at x))
subst-compose σ₁ σ₂ skip = refl
subst-compose σ₁ σ₂ ⊤ = refl
subst-compose σ₁ σ₂ 𝟘 = refl
subst-compose σ₁ σ₂ ⊥ = refl
subst-compose σ₁ σ₂ 𝟙 = refl
subst-compose σ₁ σ₂ (A ⨟ B) = cong₂ _⨟_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (A & B) = cong₂ _&_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (A ⊕ B) = cong₂ _⊕_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (A ⅋ B) = cong₂ _⅋_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (A ⊗ B) = cong₂ _⊗_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (get μ) = refl
subst-compose σ₁ σ₂ (put μ) = refl
subst-compose σ₁ σ₂ (inv x) = refl
subst-compose σ₁ σ₂ (rec A) = cong rec (subst-compose σ₁ σ₂ A)

IdentitySubstitution : ∀{n r s} → ℕ → (Fin r → PreType n s) → Set
IdentitySubstitution {_} {r} {s} k τ = ∀{x : Fin r} → toℕ x < k → τ x == inv x

id-zero : ∀{n r s} (τ : Fin r → PreType n s) → IdentitySubstitution 0 τ
id-zero τ ()

exts-id : ∀{n r s k} {τ : Fin r → PreType n s} → IdentitySubstitution k τ → IdentitySubstitution (suc k) (exts τ)
exts-id iτ {zero} x<k = inv refl
exts-id iτ {suc x} (_≤_.s≤s x<k) = rename== suc suc (cong suc) (iτ x<k)

rec-subst-== : ∀{n r s t}
        {τ : Fin r → PreType n s} → IdentitySubstitution t τ →
        {A : PreType n r} {B : PreType n t} → A == B → rec-subst τ A == A
rec-subst-== iτ skip = skip
rec-subst-== iτ bot = bot
rec-subst-== iτ one = one
rec-subst-== iτ top = top
rec-subst-== iτ zero = zero
rec-subst-== iτ put = put
rec-subst-== iτ get = get
rec-subst-== iτ var = var
rec-subst-== iτ rav = rav
rec-subst-== iτ (seq eq eq₁) = seq (rec-subst-== iτ eq) (rec-subst-== iτ eq₁)
rec-subst-== iτ (par eq eq₁) = par (rec-subst-== iτ eq) (rec-subst-== iτ eq₁)
rec-subst-== iτ (ten eq eq₁) = ten (rec-subst-== iτ eq) (rec-subst-== iτ eq₁)
rec-subst-== iτ (amp eq eq₁) = amp (rec-subst-== iτ eq) (rec-subst-== iτ eq₁)
rec-subst-== iτ (plus eq eq₁) = plus (rec-subst-== iτ eq) (rec-subst-== iτ eq₁)
rec-subst-== iτ (inv {x} {y} eq) = iτ (Eq.subst (_< _) (sym eq) (Fin.toℕ<n y))
rec-subst-== iτ (rec eq) = rec (rec-subst-== (exts-id iτ) eq)

rec-subst-≡ : ∀{m n r s} (τ : Fin r → PreType n s) (σ : Substitution m n) →
               (x : Fin m) → rec-subst τ (σ .at {r} x) ≡ σ .at {s} x
rec-subst-≡ {_} {_} {r} {s} τ σ x = ==≡ (==trans (rec-subst-== (id-zero τ) (σ .co x)) (σ .co x))

rename-≡ : ∀{m n r s} (ρ : Renaming r s) (σ : Substitution m n) →
            (x : Fin m) → rename ρ (σ .at x) ≡ σ .at x
rename-≡ ρ σ x =
  begin
    rename ρ (σ .at x) ≡⟨ rename-as-subst ρ (σ .at x) ⟩
    rec-subst (inv ∘ ρ) (σ .at x) ≡⟨ rec-subst-≡ (inv ∘ ρ) σ x ⟩
    σ .at x ∎
  where open Eq.≡-Reasoning

rename-subst : ∀{m n r s} (ρ : Renaming r s) (σ : Substitution m n) →
               (A : PreType m r) → rename ρ (subst σ A) ≡ subst σ (rename ρ A)
rename-subst ρ σ (var x) = rename-≡ ρ σ x
rename-subst ρ σ (rav x) = rename-≡ ρ (Dual σ) x
rename-subst ρ σ skip = refl
rename-subst ρ σ ⊤ = refl
rename-subst ρ σ 𝟘 = refl
rename-subst ρ σ ⊥ = refl
rename-subst ρ σ 𝟙 = refl
rename-subst ρ σ (A ⨟ B) = cong₂ _⨟_ (rename-subst ρ σ A) (rename-subst ρ σ B)
rename-subst ρ σ (A & B) = cong₂ _&_ (rename-subst ρ σ A) (rename-subst ρ σ B)
rename-subst ρ σ (A ⊕ B) = cong₂ _⊕_ (rename-subst ρ σ A) (rename-subst ρ σ B)
rename-subst ρ σ (A ⅋ B) = cong₂ _⅋_ (rename-subst ρ σ A) (rename-subst ρ σ B)
rename-subst ρ σ (A ⊗ B) = cong₂ _⊗_ (rename-subst ρ σ A) (rename-subst ρ σ B)
rename-subst ρ σ (get x) = refl
rename-subst ρ σ (put x) = refl
rename-subst ρ σ (inv x) = refl
rename-subst ρ σ (rec A) = cong rec (rename-subst (ext ρ) σ A)

exts-subst : ∀{m n r s} (τ : Fin r → PreType m s)
             (σ : Substitution m n) →
             exts (subst σ ∘ τ) ≡ subst σ ∘ exts τ
exts-subst τ closed = extensionality (aux τ closed)
  where
    aux : ∀{m n r s} (τ : Fin r → PreType m s) (σ : Substitution m n) →
          (x : Fin (suc r)) → exts (subst σ ∘ τ) x ≡ subst σ (exts τ x)
    aux τ σ zero = refl
    aux τ σ (suc x) = rename-subst suc σ (τ x)

rec-subst-subst : ∀{m n r s} (τ : Fin r → PreType m s)
                  (σ : Substitution m n) →
                  (A : PreType m r) → rec-subst (subst σ ∘ τ) (subst σ A) ≡ subst σ (rec-subst τ A)
rec-subst-subst τ σ (var x) = rec-subst-≡ (subst σ ∘ τ) σ x
rec-subst-subst τ σ (rav x) = rec-subst-≡ (subst σ ∘ τ) (Dual σ) x
rec-subst-subst τ σ skip = refl
rec-subst-subst τ σ ⊤ = refl
rec-subst-subst τ σ 𝟘 = refl
rec-subst-subst τ σ ⊥ = refl
rec-subst-subst τ σ 𝟙 = refl
rec-subst-subst τ σ (A ⨟ B) = cong₂ _⨟_ (rec-subst-subst τ σ A) (rec-subst-subst τ σ B)
rec-subst-subst τ σ (A & B) = cong₂ _&_ (rec-subst-subst τ σ A) (rec-subst-subst τ σ B)
rec-subst-subst τ σ (A ⊕ B) = cong₂ _⊕_ (rec-subst-subst τ σ A) (rec-subst-subst τ σ B)
rec-subst-subst τ σ (A ⅋ B) = cong₂ _⅋_ (rec-subst-subst τ σ A) (rec-subst-subst τ σ B)
rec-subst-subst τ σ (A ⊗ B) = cong₂ _⊗_ (rec-subst-subst τ σ A) (rec-subst-subst τ σ B)
rec-subst-subst τ σ (get x) = refl
rec-subst-subst τ σ (put x) = refl
rec-subst-subst τ σ (inv x) = refl
rec-subst-subst τ σ (rec A) rewrite exts-subst τ σ = cong rec (rec-subst-subst (exts τ) σ A)

s-just-subst : ∀{m n r} (σ : Substitution m n) →
               (A : PreType m r) → s-just (subst σ A) ≡ subst σ ∘ s-just A
s-just-subst {m} {n} {r} σ A = extensionality aux
  where
    aux : ∀(x : Fin (suc r)) → s-just (subst σ A) x ≡ subst σ (s-just A x)
    aux zero = refl
    aux (suc x) = refl

unfold-subst : ∀{m n r} (σ : Substitution m n) →
               (A : PreType m (suc r)) → unfold (subst σ A) ≡ subst σ (unfold A)
unfold-subst {m} {n} {r} σ A =
  begin
    unfold (subst σ A) ≡⟨⟩
    rec-subst (s-just (rec (subst σ A))) (subst σ A) ≡⟨⟩
    rec-subst (s-just (subst σ (rec A))) (subst σ A) ≡⟨ cong (λ x → rec-subst x (subst σ A)) (s-just-subst σ (rec A)) ⟩
    rec-subst (subst σ ∘ s-just (rec A)) (subst σ A) ≡⟨ rec-subst-subst (s-just (rec A)) σ A ⟩
    subst σ (rec-subst (s-just (rec A)) A) ≡⟨⟩
    subst σ (unfold A)
  ∎
  where
    open Eq.≡-Reasoning
