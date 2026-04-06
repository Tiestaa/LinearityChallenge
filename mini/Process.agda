{-# OPTIONS --rewriting #-}
open import Data.Unit using (tt)
open import Data.Sum
open import Data.Product using (_,_)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Unary

open import Type
open import Context
open import Permutations

data Ch (A : Type) : Context → Set where
  ch : Ch A [ A ]

data Proc : Context → Set where
  link     : ∀{A} → ∀[ Ch A ∗ Ch (dual A) ⇒ Proc ]
  fail     : ∀[ Ch ⊤ ∗ U ⇒ Proc ]
  wait     : ∀[ Ch ⊥ ∗ Proc ⇒ Proc ]
  close    : ∀[ Ch 𝟙 ⇒ Proc ]
  case     : ∀{A B} → ∀[ Ch (A & B) ∗ ((A ∷_) ⊢ Proc ∩ (B ∷_) ⊢ Proc) ⇒ Proc ]
  select   : ∀{A B} → ∀[ Ch (A ⊕ B) ∗ ((A ∷_) ⊢ Proc ∪ (B ∷_) ⊢ Proc) ⇒ Proc ]
  join     : ∀{A B} → ∀[ Ch (A ⅋ B) ∗ ((A ∷_) ⊢ (B ∷_) ⊢ Proc) ⇒ Proc ]
  fork     : ∀{A B} → ∀[ Ch (A ⊗ B) ∗ ((A ∷_) ⊢ Proc) ∗ ((B ∷_) ⊢ Proc) ⇒ Proc ]
  cut      : ∀{A} → ∀[ ((A ∷_) ⊢ Proc) ∗ ((dual A ∷_) ⊢ Proc) ⇒ Proc ]

↭proc : ∀{Γ Δ} → Γ ↭ Δ → Proc Γ → Proc Δ
↭proc π (link (ch ⟨ p ⟩ ch)) with ↭solo π p
... | _ , q , π' rewrite ↭solo-inv π' = link (ch ⟨ q ⟩ ch)
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
↭proc π (cut (P ⟨ p ⟩ Q)) with ↭split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut (↭proc (prep π₁) P ⟨ q ⟩ ↭proc (prep π₂) Q)
