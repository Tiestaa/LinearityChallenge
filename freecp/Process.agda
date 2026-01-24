{-# OPTIONS --rewriting --guardedness #-}
open import Function using (_∘_)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.List.Base using (List; []; _∷_; [_])
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Type
open import Type.Equivalence
open import Type.Substitutions
open import Context
open import Permutations

record ProcType : Set where
  field
    {n} : ℕ
    measure : ℕ
    context : Context n

open ProcType

ProcContext : Set
ProcContext = List ProcType

data _∈_ (T : ProcType) : ProcContext → Set where
  here : ∀{Σ} → T ∈ (T ∷ Σ)
  next : ∀{S Σ} → T ∈ Σ → T ∈ (S ∷ Σ)

data Ch {n} (A : Type n) : Context n → Set where
  ch : Ch A [ A ]

data Proc {n} (Σ : ProcContext) : ℕ → Context n → Set where
  call     : ∀{T} → T ∈ Σ →
             {σ : Substitution (T .ProcType.n) n} → ClosedSubstitution σ →
             ∀[ substc σ (T .context) ↭_ ⇒ Proc Σ (suc (T .measure)) ]
  link     : ∀{A B μ} → dual A ≈ B → ∀[ Ch A ∗ Ch B ⇒ Proc Σ (suc μ) ]
  fail     : ∀{μ} → ∀[ Ch ⊤ ∗ U ⇒ Proc Σ μ ]
  wait     : ∀{μ} → ∀[ Ch ⊥ ∗ Proc Σ μ ⇒ Proc Σ μ ]
  close    : ∀{μ} → ∀[ Ch 𝟙 ⇒ Proc Σ (suc μ) ]
  case     : ∀{A B μ} → ∀[ Ch (A & B) ∗ ((A ∷_) ⊢ Proc Σ μ ∩ (B ∷_) ⊢ Proc Σ μ) ⇒ Proc Σ μ ]
  select   : ∀{A B μ} → ∀[ Ch (A ⊕ B) ∗ ((A ∷_) ⊢ Proc Σ μ ∪ (B ∷_) ⊢ Proc Σ μ) ⇒ Proc Σ (suc μ) ]
  join     : ∀{A B μ} → ∀[ Ch (A ⅋ B) ∗ ((B ∷_) ⊢ (A ∷_) ⊢ Proc Σ μ) ⇒ Proc Σ μ ]
  fork     : ∀{A B μ ν} → ∀[ Ch (A ⊗ B) ∗ ((A ∷_) ⊢ Proc Σ μ) ∗ ((B ∷_) ⊢ Proc Σ ν) ⇒ Proc Σ (suc μ + ν) ]
  put      : ∀{A μ ω} → ∀[ Ch (put ω ⨟ A) ∗ ((A ∷_) ⊢ Proc Σ μ) ⇒ Proc Σ (suc μ + ω) ]
  get      : ∀{A μ ν ω} → μ ≡ ν + ω → ∀[ Ch (get ω ⨟ A) ∗ ((A ∷_) ⊢ Proc Σ μ) ⇒ Proc Σ ν ]
  cut      : ∀{A B μ ν} → dual A ≈ B → ∀[ ((A ∷_) ⊢ Proc Σ μ) ∗ ((B ∷_) ⊢ Proc Σ ν) ⇒ Proc Σ (μ + ν) ]

Def : ProcContext → Set
Def Σ = ∀{T} → T ∈ Σ → Proc Σ (T .measure) (T .context)

↭proc : ∀{n} {Γ Δ : Context n} {Σ μ} → Γ ↭ Δ → Proc Σ μ Γ → Proc Σ μ Δ
↭proc π (call x σ π') = call x σ (trans π' π)
↭proc π (link eq (ch ⟨ p ⟩ ch)) with ↭solo π p
... | _ , q , π' rewrite ↭solo-inv π' = link eq (ch ⟨ q ⟩ ch)
↭proc π (fail (ch ⟨ p ⟩ tt)) with ↭solo π p
... | _ , q , π' = fail (ch ⟨ q ⟩ tt)
↭proc π (wait (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = wait (ch ⟨ q ⟩ ↭proc π' P)
↭proc π (close ch) rewrite ↭solo-inv π = close ch
↭proc π (case (ch ⟨ p ⟩ (P , Q))) with ↭solo π p
... | _ , q , π' = case (ch ⟨ q ⟩ (↭proc (prep π') P , ↭proc (prep π') Q))
↭proc π (select (ch ⟨ p ⟩ inj₁ P)) with ↭solo π p
... | _ , q , π' = select (ch ⟨ q ⟩ inj₁ (↭proc (prep π') P))
↭proc π (select (ch ⟨ p ⟩ inj₂ P)) with ↭solo π p
... | _ , q , π' = select (ch ⟨ q ⟩ inj₂ (↭proc (prep π') P))
↭proc π (join (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = join (ch ⟨ q ⟩ ↭proc (prep (prep π')) P)
↭proc π (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) with ↭solo π p
... | _ , p' , π' with ↭split π' q
... | Δ₁ , Δ₂ , q' , π₁ , π₂ = fork (ch ⟨ p' ⟩ (↭proc (prep π₁) P ⟨ q' ⟩ ↭proc (prep π₂) Q))
↭proc π (put (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = put (ch ⟨ q ⟩ ↭proc (prep π') P)
↭proc π (get eq (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = get eq (ch ⟨ q ⟩ ↭proc (prep π') P)
↭proc π (cut eq (P ⟨ p ⟩ Q)) with ↭split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut eq (↭proc (prep π₁) P ⟨ q ⟩ ↭proc (prep π₂) Q)

substp : ∀{n m Σ μ} {Γ : Context n}
         {σ : Substitution n m} → ClosedSubstitution σ →
         Proc Σ μ Γ → Proc Σ μ (substc σ Γ)
substp {σ = σ} σc (call {T} x {σ = σ'} cσ' π) with ↭subst σ π
... | π' rewrite substc-compose σ' σ (T .context) = call x (subst-cs cσ' σc) π'
substp {σ = σ} σc (link {A} eq (ch ⟨ p ⟩ ch)) with ≈subst σc eq
... | eq' rewrite sym (dual-subst σ A) = link eq' (ch ⟨ +-subst σ p ⟩ ch)
substp {σ = σ} σc (fail (ch ⟨ p ⟩ tt)) = fail (ch ⟨ +-subst σ p ⟩ tt)
substp {σ = σ} σc (wait (ch ⟨ p ⟩ P)) = wait (ch ⟨ +-subst σ p ⟩ substp σc P)
substp _ (close ch) = close ch
substp {σ = σ} σc (case (ch ⟨ p ⟩ (P , Q))) = case (ch ⟨ +-subst σ p ⟩ (substp σc P , substp σc Q))
substp {σ = σ} σc (select (ch ⟨ p ⟩ inj₁ P)) = select (ch ⟨ +-subst σ p ⟩ inj₁ (substp σc P))
substp {σ = σ} σc (select (ch ⟨ p ⟩ inj₂ Q)) = select (ch ⟨ +-subst σ p ⟩ inj₂ (substp σc Q))
substp {σ = σ} σc (join (ch ⟨ p ⟩ P)) = join (ch ⟨ +-subst σ p ⟩ substp σc P)
substp {σ = σ} σc (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) = fork (ch ⟨ +-subst σ p ⟩ (substp σc P ⟨ +-subst σ q ⟩ substp σc Q))
substp {σ = σ} σc (put (ch ⟨ p ⟩ P)) = put (ch ⟨ +-subst σ p ⟩ substp σc P)
substp {σ = σ} σc (get eq (ch ⟨ p ⟩ P)) = get eq (ch ⟨ +-subst σ p ⟩ substp σc P)
substp {σ = σ} σc (cut {A} eq (P ⟨ p ⟩ Q)) with ≈subst σc eq
... | eq' rewrite sym (dual-subst σ A) = cut eq' (substp σc P ⟨ +-subst σ p ⟩ substp σc Q)
