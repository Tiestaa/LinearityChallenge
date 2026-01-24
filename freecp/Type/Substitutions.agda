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

==subst : ∀{m n r s} (σ : Substitution m n) {A : PreType m r} {B : PreType m s} →
          A == B → subst σ A == subst σ B
==subst σ skip = skip
==subst σ bot = bot
==subst σ one = one
==subst σ top = top
==subst σ zero = zero
==subst σ put = put
==subst σ get = get
==subst σ var = σ .co _
==subst σ rav = dual== (σ .co _)
==subst σ (seq x y) = seq (==subst σ x) (==subst σ y)
==subst σ (par x y) = par (==subst σ x) (==subst σ y)
==subst σ (ten x y) = ten (==subst σ x) (==subst σ y)
==subst σ (amp x y) = amp (==subst σ x) (==subst σ y)
==subst σ (plus x y) = plus (==subst σ x) (==subst σ y)
==subst σ (inv x) = inv x
==subst σ (rec x) = rec (==subst σ x)

_·_ : ∀{m n o} → Substitution n o → Substitution m n → Substitution m o
(τ · σ) .at = subst τ ∘ σ .at
(τ · σ) .co = ==subst τ ∘ σ .co

Dual : ∀{m n} → Substitution m n → Substitution m n
Dual σ .at = dual ∘ σ .at
Dual σ .co x = dual== (σ .co x)

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
exts-id iτ {suc x} (_≤_.s≤s x<k) with iτ x<k
... | p = ==trans (rename== suc suc same-suc-suc p) (inv refl)

data Closed {n r} (k : ℕ) : PreType n r → Set where
  skip : Closed k skip
  bot  : Closed k ⊥
  one  : Closed k 𝟙
  top  : Closed k ⊤
  zero : Closed k 𝟘
  put  : ∀{μ} → Closed k (put μ)
  get  : ∀{μ} → Closed k (get μ)
  var  : ∀{x} → Closed k (var x)
  rav  : ∀{x} → Closed k (rav x)
  seq  : ∀{A B} → Closed k A → Closed k B → Closed k (A ⨟ B)
  par  : ∀{A B} → Closed k A → Closed k B → Closed k (A ⅋ B)
  ten  : ∀{A B} → Closed k A → Closed k B → Closed k (A ⊗ B)
  amp  : ∀{A B} → Closed k A → Closed k B → Closed k (A & B)
  plus : ∀{A B} → Closed k A → Closed k B → Closed k (A ⊕ B)
  inv  : ∀{x} → toℕ x < k → Closed k (inv x)
  rec  : ∀{A} → Closed (suc k) A → Closed k (rec A)

Closed-dual : ∀{n r} {k : ℕ} {A : PreType n r} → Closed k A → Closed k (dual A)
Closed-dual skip = skip
Closed-dual bot = one
Closed-dual one = bot
Closed-dual top = zero
Closed-dual zero = top
Closed-dual put = get
Closed-dual get = put
Closed-dual var = rav
Closed-dual rav = var
Closed-dual (seq x y) = seq (Closed-dual x) (Closed-dual y)
Closed-dual (par x y) = ten (Closed-dual x) (Closed-dual y)
Closed-dual (ten x y) = par (Closed-dual x) (Closed-dual y)
Closed-dual (amp x y) = plus (Closed-dual x) (Closed-dual y)
Closed-dual (plus x y) = amp (Closed-dual x) (Closed-dual y)
Closed-dual (inv x) = inv x
Closed-dual (rec x) = rec (Closed-dual x)

rec-subst-Closed : ∀{n r s t}
                   (k : ℕ)
                   {τ : Fin r → PreType n s} → IdentitySubstitution k τ →
                   {A : PreType n r} {B : PreType n t} → Closed k A → A == B →
                   rec-subst τ A == B
rec-subst-Closed k iτ ca skip = skip
rec-subst-Closed k iτ ca bot = bot
rec-subst-Closed k iτ ca one = one
rec-subst-Closed k iτ ca top = top
rec-subst-Closed k iτ ca zero = zero
rec-subst-Closed k iτ ca put = put
rec-subst-Closed k iτ ca get = get
rec-subst-Closed k iτ ca var = var
rec-subst-Closed k iτ ca rav = rav
rec-subst-Closed k iτ (seq ca cb) (seq x y) = seq (rec-subst-Closed k iτ ca x) (rec-subst-Closed k iτ cb y)
rec-subst-Closed k iτ (par ca cb) (par x y) = par (rec-subst-Closed k iτ ca x) (rec-subst-Closed k iτ cb y)
rec-subst-Closed k iτ (ten ca cb) (ten x y) = ten (rec-subst-Closed k iτ ca x) (rec-subst-Closed k iτ cb y)
rec-subst-Closed k iτ (amp ca cb) (amp x y) = amp (rec-subst-Closed k iτ ca x) (rec-subst-Closed k iτ cb y)
rec-subst-Closed k iτ (plus ca cb) (plus x y) = plus (rec-subst-Closed k iτ ca x) (rec-subst-Closed k iτ cb y)
rec-subst-Closed k iτ (inv x<k) (inv eq) = ==trans (iτ x<k) (inv eq)
rec-subst-Closed k iτ (rec ca) (rec x) = rec (rec-subst-Closed (suc k) (exts-id iτ) ca x)

==Closed : ∀{n r k} {A : PreType n r} {B : PreType n k} → A == B → Closed k A
==Closed skip = skip
==Closed bot = bot
==Closed one = one
==Closed top = top
==Closed zero = zero
==Closed put = put
==Closed get = get
==Closed var = var
==Closed rav = rav
==Closed (seq x y) = seq (==Closed x) (==Closed y)
==Closed (par x y) = par (==Closed x) (==Closed y)
==Closed (ten x y) = ten (==Closed x) (==Closed y)
==Closed (amp x y) = amp (==Closed x) (==Closed y)
==Closed (plus x y) = plus (==Closed x) (==Closed y)
==Closed {k = k} (inv {x} {y} x≡y) with Fin.toℕ<n y
... | y<k = inv (Eq.subst (_< k) (sym x≡y) y<k)
==Closed (rec eq) = rec (==Closed eq)

rec-subst-cs : ∀{m n r s}
               (τ : Fin r → PreType n s) →
               (σ : Substitution m n) →
               (x : Fin m) → rec-subst τ (σ .at x) ≡ σ .at x
rec-subst-cs {_} {_} {r} {s} τ σ x with id-zero τ
... | iτ with rec-subst-Closed {_} {_} {_} {s} 0 iτ (==Closed (σ .co x)) (σ .co x)
... | p = ==≡ (==trans p (σ .co x))

rename-cs : ∀{m n r s} (ρ : Fin r → Fin s) →
            (σ : Substitution m n) →
            (x : Fin m) → rename ρ (σ .at x) ≡ σ .at x
rename-cs ρ σ x =
  begin
    rename ρ (σ .at x) ≡⟨ rename-as-subst ρ (σ .at x) ⟩
    rec-subst (inv ∘ ρ) (σ .at x) ≡⟨ rec-subst-cs (inv ∘ ρ) σ x ⟩
    σ .at x ∎
  where open Eq.≡-Reasoning

rename-subst : ∀{m n r s}
               (ρ : Fin r → Fin s) (σ : Substitution m n) →
               (A : PreType m r) →
               rename ρ (subst σ A) ≡ subst σ (rename ρ A)
rename-subst ρ σ (var x) = rename-cs ρ σ x
rename-subst ρ σ (rav x) = rename-cs ρ (Dual σ) x
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
rec-subst-subst τ σ (var x) = rec-subst-cs (subst σ ∘ τ) σ x
rec-subst-subst τ σ (rav x) = rec-subst-cs (subst σ ∘ τ) (Dual σ) x
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
