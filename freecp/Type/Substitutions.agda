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

SameSubstitution : ∀{m n} → Substitution m n → Substitution m n → Set
SameSubstitution {m} σ σ' = ∀{u v} (x : Fin m) → σ {u} x == σ' {v} x

ClosedSubstitution : ∀{m n} → Substitution m n → Set
ClosedSubstitution σ = SameSubstitution σ σ

skip-cs : ∀{m n} → ClosedSubstitution {m} {n} (λ _ → skip)
skip-cs _ = skip

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
               {σ : Substitution m n} → ClosedSubstitution σ →
               (x : Fin m) → rec-subst τ (σ x) ≡ σ x
rec-subst-cs {_} {_} {r} {s} τ {σ} cσ x with id-zero τ
... | iτ with rec-subst-Closed {_} {_} {_} {s} 0 iτ (==Closed (cσ x)) (cσ x)
... | p = ==≡ (==trans p (cσ x))

dual-cs : ∀{m n} {σ : Substitution m n} →
          ClosedSubstitution σ → ClosedSubstitution (dual ∘ σ)
dual-cs cσ x = dual== (cσ x)

rename-cs : ∀{m n r s} (ρ : Fin r → Fin s) →
            {σ : Substitution m n} → ClosedSubstitution σ →
            (x : Fin m) → rename ρ (σ x) ≡ σ x
rename-cs ρ {σ} cσ x =
  begin
    rename ρ (σ x) ≡⟨ rename-as-subst ρ (σ x) ⟩
    rec-subst (inv ∘ ρ) (σ x) ≡⟨ rec-subst-cs (inv ∘ ρ) cσ x ⟩
    σ x ∎
  where open Eq.≡-Reasoning

rename-subst : ∀{m n r s}
               (ρ : Fin r → Fin s) {σ : Substitution m n} →
               ClosedSubstitution σ → (A : PreType m r) →
               rename ρ (subst σ A) ≡ subst σ (rename ρ A)
rename-subst ρ cσ (var x) = rename-cs ρ cσ x
rename-subst ρ cσ (rav x) = rename-cs ρ (dual-cs cσ) x
rename-subst ρ cσ skip = refl
rename-subst ρ cσ ⊤ = refl
rename-subst ρ cσ 𝟘 = refl
rename-subst ρ cσ ⊥ = refl
rename-subst ρ cσ 𝟙 = refl
rename-subst ρ cσ (A ⨟ B) = cong₂ _⨟_ (rename-subst ρ cσ A) (rename-subst ρ cσ B)
rename-subst ρ cσ (A & B) = cong₂ _&_ (rename-subst ρ cσ A) (rename-subst ρ cσ B)
rename-subst ρ cσ (A ⊕ B) = cong₂ _⊕_ (rename-subst ρ cσ A) (rename-subst ρ cσ B)
rename-subst ρ cσ (A ⅋ B) = cong₂ _⅋_ (rename-subst ρ cσ A) (rename-subst ρ cσ B)
rename-subst ρ cσ (A ⊗ B) = cong₂ _⊗_ (rename-subst ρ cσ A) (rename-subst ρ cσ B)
rename-subst ρ cσ (get x) = refl
rename-subst ρ cσ (put x) = refl
rename-subst ρ cσ (inv x) = refl
rename-subst ρ cσ (rec A) = cong rec (rename-subst (ext ρ) cσ A)

exts-subst : ∀{m n r s} (τ : Fin r → PreType m s)
             {σ : Substitution m n} → ClosedSubstitution σ →
             exts (subst σ ∘ τ) ≡ subst σ ∘ exts τ
exts-subst τ closed = extensionality (aux τ closed)
  where
    aux : ∀{m n r s} (τ : Fin r → PreType m s)
          {σ : Substitution m n} → ClosedSubstitution σ →
          (x : Fin (suc r)) → exts (subst σ ∘ τ) x ≡ subst σ (exts τ x)
    aux τ cσ zero = refl
    aux τ cσ (suc x) = rename-subst suc cσ (τ x)

rec-subst-subst : ∀{m n r s} (τ : Fin r → PreType m s)
                  {σ : Substitution m n} → ClosedSubstitution σ →
                  (A : PreType m r) → rec-subst (subst σ ∘ τ) (subst σ A) ≡ subst σ (rec-subst τ A)
rec-subst-subst τ {σ} cσ (var x) = rec-subst-cs (subst σ ∘ τ) cσ x
rec-subst-subst τ {σ} cσ (rav x) = rec-subst-cs (subst σ ∘ τ) (dual-cs cσ) x
rec-subst-subst τ cσ skip = refl
rec-subst-subst τ cσ ⊤ = refl
rec-subst-subst τ cσ 𝟘 = refl
rec-subst-subst τ cσ ⊥ = refl
rec-subst-subst τ cσ 𝟙 = refl
rec-subst-subst τ cσ (A ⨟ B) = cong₂ _⨟_ (rec-subst-subst τ cσ A) (rec-subst-subst τ cσ B)
rec-subst-subst τ cσ (A & B) = cong₂ _&_ (rec-subst-subst τ cσ A) (rec-subst-subst τ cσ B)
rec-subst-subst τ cσ (A ⊕ B) = cong₂ _⊕_ (rec-subst-subst τ cσ A) (rec-subst-subst τ cσ B)
rec-subst-subst τ cσ (A ⅋ B) = cong₂ _⅋_ (rec-subst-subst τ cσ A) (rec-subst-subst τ cσ B)
rec-subst-subst τ cσ (A ⊗ B) = cong₂ _⊗_ (rec-subst-subst τ cσ A) (rec-subst-subst τ cσ B)
rec-subst-subst τ cσ (get x) = refl
rec-subst-subst τ cσ (put x) = refl
rec-subst-subst τ cσ (inv x) = refl
rec-subst-subst τ cσ (rec A) rewrite exts-subst τ cσ = cong rec (rec-subst-subst (exts τ) cσ A)

s-just-subst : ∀{m n r} (σ : Substitution m n) →
               (A : PreType m r) → s-just (subst σ A) ≡ subst σ ∘ s-just A
s-just-subst {m} {n} {r} σ A = extensionality aux
  where
    aux : ∀(x : Fin (suc r)) → s-just (subst σ A) x ≡ subst σ (s-just A x)
    aux zero = refl
    aux (suc x) = refl

unfold-subst : ∀{m n r} {σ : Substitution m n} → ClosedSubstitution σ →
               (A : PreType m (suc r)) → unfold (subst σ A) ≡ subst σ (unfold A)
unfold-subst {m} {n} {r} {σ} closed A =
  begin
    unfold (subst σ A) ≡⟨⟩
    rec-subst (s-just (rec (subst σ A))) (subst σ A) ≡⟨⟩
    rec-subst (s-just (subst σ (rec A))) (subst σ A) ≡⟨ cong (λ x → rec-subst x (subst σ A)) (s-just-subst σ (rec A)) ⟩
    rec-subst (subst σ ∘ s-just (rec A)) (subst σ A) ≡⟨ rec-subst-subst (s-just (rec A)) closed A ⟩
    subst σ (rec-subst (s-just (rec A)) A) ≡⟨⟩
    subst σ (unfold A)
  ∎
  where
    open Eq.≡-Reasoning

same-substitutions : ∀{m n r s} {σ τ : Substitution m n}
                     {A : PreType m r} {B : PreType m s} → A == B →
                     SameSubstitution σ τ → subst σ A == subst τ B
same-substitutions skip same = skip
same-substitutions bot same = bot
same-substitutions one same = one
same-substitutions top same = top
same-substitutions zero same = zero
same-substitutions put same = put
same-substitutions get same = get
same-substitutions var same = same _
same-substitutions rav same = dual== (same _)
same-substitutions (seq x x₁) same = seq (same-substitutions x same) (same-substitutions x₁ same)
same-substitutions (par x x₁) same = par (same-substitutions x same) (same-substitutions x₁ same)
same-substitutions (ten x x₁) same = ten (same-substitutions x same) (same-substitutions x₁ same)
same-substitutions (amp x x₁) same = amp (same-substitutions x same) (same-substitutions x₁ same)
same-substitutions (plus x x₁) same = plus (same-substitutions x same) (same-substitutions x₁ same)
same-substitutions (inv x) same = inv x
same-substitutions (rec x) same = rec (same-substitutions x same)

same-substitutions-id : ∀{m n} {σ : Substitution m n} →
                        ClosedSubstitution σ → SameSubstitution σ σ
same-substitutions-id cσ x = cσ x

subst-cs : ∀{m n o}
           {σ : Substitution m n} → ClosedSubstitution σ →
           {τ : Substitution n o} → ClosedSubstitution τ →
           ClosedSubstitution (subst τ ∘ σ)
subst-cs {σ = σ} cσ {τ} cτ {u} {v} x = same-substitutions (cσ x) (same-substitutions-id cτ)

