{-# OPTIONS --rewriting --guardedness #-}
module Type.HeadNormalForm where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite

open import Axioms
open import Type
open import Type.Transitions
open import Type.Equivalence
open import Type.Substitutions

data Visible {n r} (A : PreType n r) : Set where
  visible : ∀{m ℓ B} {σ : ∀{u} → Fin n → PreType m u} → ClosedSubstitution σ → subst σ A ⊨ ℓ ⇒ B → Visible A

data HeadNormalForm {n r} : PreType n r → Set where
  null : HeadNormalForm void
  skip : HeadNormalForm skip
  bot  : HeadNormalForm ⊥
  one  : HeadNormalForm 𝟙
  top  : HeadNormalForm ⊤
  zero : HeadNormalForm 𝟘
  put  : ∀{A μ} → HeadNormalForm (put μ ⨟ A)
  get  : ∀{A μ} → HeadNormalForm (get μ ⨟ A)
  var  : ∀{A x} → HeadNormalForm (var x ⨟ A)
  rav  : ∀{A x} → HeadNormalForm (rav x ⨟ A)
  par  : ∀{A B} → HeadNormalForm (A ⅋ B)
  ten  : ∀{A B} → HeadNormalForm (A ⊗ B)
  amp  : ∀{A B} → HeadNormalForm (A & B)
  plus : ∀{A B} → HeadNormalForm (A ⊕ B)

nfseq : ∀{n} {A : Type n} → HeadNormalForm A → {B : Type n} → A ≡ skip ⊎ ∃[ N ] HeadNormalForm {n} {0} N × (A ⨟ B) ≈ N
nfseq null = inj₂ (void , null , void⨟A≈void)
nfseq skip = inj₁ refl
nfseq bot = inj₂ (_ , bot , ≈⊥)
nfseq one = inj₂ (_ , one , ≈𝟙)
nfseq top = inj₂ (_ , top , ≈⊤)
nfseq zero = inj₂ (_ , zero , ≈𝟘)
nfseq put = inj₂ (_ , put , ≈sym ≈assoc)
nfseq get = inj₂ (_ , get , ≈sym ≈assoc)
nfseq var = inj₂ (_ , var , ≈sym ≈assoc)
nfseq rav = inj₂ (_ , rav , ≈sym ≈assoc)
nfseq par = inj₂ (_ , par , ≈⅋⨟)
nfseq ten = inj₂ (_ , ten , ≈⊗⨟)
nfseq amp = inj₂ (_ , amp , ≈dist&)
nfseq plus = inj₂ (_ , plus , ≈dist⊕)

skip-transition : ∀{m n ℓ B} {A : Type m} → A ≈ skip →
                  {σ : ∀{u} → Fin m → PreType n u} → ClosedSubstitution σ →
                  subst σ A ⊨ ℓ ⇒ B → ℓ ≡ ε
skip-transition eq cσ tr with eq .from cσ .Sim.next skip
... | _ , tr' , _ = only-skip tr' tr

nf-transition : ∀{m n ℓ B} (A : Type m)
                {σ : ∀{u} → Fin m → PreType n u} → ClosedSubstitution σ →
                subst σ A ⊨ ℓ ⇒ B → ∃[ N ] HeadNormalForm N × A ≈ N
nf-transition (var x) cσ tr = _ , var , A≈A⨟skip
nf-transition (rav x) cσ tr = _ , rav , A≈A⨟skip
nf-transition skip cσ tr = _ , skip , ≈refl
nf-transition ⊤ cσ tr = _ , top , ≈refl
nf-transition 𝟘 cσ tr = _ , zero , ≈refl
nf-transition ⊥ cσ tr = _ , bot , ≈refl
nf-transition 𝟙 cσ tr = _ , one , ≈refl
nf-transition (A ⨟ B) cσ (seq tr ns) with nf-transition A cσ tr
... | N , anf , aeq with nfseq anf {B}
... | inj₂ (N' , nf , eq) = N' , nf , ≈trans (≈cong⨟ aeq ≈refl) eq
... | inj₁ refl with skip-transition aeq cσ tr
... | refl = contradiction ε ns
nf-transition (A ⨟ B) cσ (seqε sk tr) with nf-transition A cσ sk
... | _ , anf , aeq with nfseq anf {B}
... | inj₂ (_ , nf , eq) = _ , nf , ≈trans (≈cong⨟ aeq ≈refl) eq
... | inj₁ refl with nf-transition B cσ tr
... | _ , bnf , beq = _ , bnf , ≈trans (≈cong⨟ aeq beq) (≈sym A≈skip⨟A)
nf-transition (A ⨟ B) cσ (seq⊗ tr) with nf-transition A cσ tr
... | _ , anf , aeq with nfseq anf {B}
... | inj₂ (_ , nf , eq) = _ , nf , ≈trans (≈cong⨟ aeq ≈refl) eq
... | inj₁ refl with skip-transition aeq cσ tr
... | ()
nf-transition (A ⨟ B) cσ (seq⅋ tr) with nf-transition A cσ tr
... | _ , anf , aeq with nfseq anf {B}
... | inj₂ (_ , nf , eq) = _ , nf , ≈trans (≈cong⨟ aeq ≈refl) eq
... | inj₁ refl with skip-transition aeq cσ tr
... | ()
nf-transition (A & B) cσ tr = _ , amp , ≈refl
nf-transition (A ⊕ B) cσ tr = _ , plus , ≈refl
nf-transition (A ⅋ B) cσ tr = _ , par , ≈refl
nf-transition (A ⊗ B) cσ tr = _ , ten , ≈refl
nf-transition (get x) cσ tr = _ , get , A≈A⨟skip
nf-transition (put x) cσ tr = _ , put , A≈A⨟skip
nf-transition (rec A) cσ (rec tr)
  rewrite unfold-subst cσ A with nf-transition (unfold A) cσ tr
... | N , nf , eq = N , nf , ≈trans ≈rec eq

nf-visible : ∀{n} (A : Type n) → Visible A → ∃[ N ] HeadNormalForm N × A ≈ N
nf-visible A (visible cσ tr) = nf-transition A cσ tr

nf-invisible : ∀{n} {A : Type n} → ¬ Visible A → A ≈ void
nf-invisible {A = A} nv .to {σ = σ} cσ .Sim.next {ℓ} {A'} tr = contradiction (visible cσ tr) nv
nf-invisible nv .from cσ .Sim.next tr = contradiction tr void-no-transitions

normal-form : ∀{n} (A : Type n) → ∃[ N ] HeadNormalForm N × A ≈ N
normal-form A with excluded-middle (Visible A)
... | inj₁ vis = nf-visible A vis
... | inj₂ nv = _ , null , nf-invisible nv
