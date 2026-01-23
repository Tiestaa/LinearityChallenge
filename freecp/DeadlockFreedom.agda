{-# OPTIONS --rewriting --guardedness #-}
open import Data.Unit using (tt)
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax)
open import Data.Nat using (suc; _+_)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Type
open import Type.Equivalence
open import Context
open import Process hiding (_∈_)
open import Reduction
open import Congruence

data Link {n Σ} : ∀{μ Γ} → Proc {n} Σ μ Γ → Set where
  link : ∀{Γ A B μ} (eq : dual A ≈ B) (p : Γ ≃ [ A ] + [ B ]) → Link (link {μ = μ} eq (ch ⟨ p ⟩ ch))

data Input {n Σ} : ∀{μ Γ} → Proc {n} Σ μ Γ → Set where
  fail : ∀{Γ Δ μ} (p : Γ ≃ [] + Δ) → Input (fail {μ = μ} (ch ⟨ < p ⟩ tt))
  wait : ∀{Γ Δ μ} {P : Proc Σ μ Δ} (p : Γ ≃ [] + Δ) → Input (wait (ch ⟨ < p ⟩ P))
  case : ∀{Γ Δ A B μ} {P : Proc Σ μ (A ∷ Δ)} {Q : Proc Σ μ (B ∷ Δ)} (p : Γ ≃ [] + Δ) → Input (case (ch ⟨ < p ⟩ (P , Q)))
  join : ∀{Γ Δ A B μ} {P : Proc Σ μ (A ∷ B ∷ Δ)} (p : Γ ≃ [] + Δ) → Input (join (ch ⟨ < p ⟩ P))
  get  : ∀{Γ Δ A μ ν ω} {P : Proc Σ μ (A ∷ Δ)} (eq : μ ≡ ν + ω) (p : Γ ≃ [] + Δ) → Input (get {ω = ω} eq (ch ⟨ < p ⟩ P))

data Output {n Σ} : ∀{μ Γ} → Proc {n} Σ μ Γ → Set where
  close    : ∀{μ} → Output (close {μ = μ} ch)
  select-l : ∀{Γ Δ A B μ} {P : Proc Σ μ (A ∷ Δ)} (p : Γ ≃ [] + Δ) → Output (select {B = B} (ch ⟨ < p ⟩ inj₁ P))
  select-r : ∀{Γ Δ A B μ} {P : Proc Σ μ (B ∷ Δ)} (p : Γ ≃ [] + Δ) → Output (select {A = A} (ch ⟨ < p ⟩ inj₂ P))
  fork     : ∀{Γ Δ Δ₁ Δ₂ A B μ ν} {P : Proc Σ μ (A ∷ Δ₁)} {Q : Proc Σ ν (B ∷ Δ₂)} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂) → Output (fork (ch ⟨ < p ⟩ (P ⟨ q ⟩ Q)))
  put      : ∀{Γ Δ A μ ω} {P : Proc Σ μ (A ∷ Δ)} (p : Γ ≃ [] + Δ) → Output (put {ω = ω} (ch ⟨ < p ⟩ P))

data Delayed {n Σ} : ∀{μ Γ} → Proc {n} Σ μ Γ → Set where
  fail     : ∀{C Γ Δ μ} (p : Γ ≃ [ ⊤ ] + Δ) → Delayed (fail {μ = μ} (ch ⟨ >_ {_} {C} p ⟩ tt))
  wait     : ∀{C Γ Δ μ} {P : Proc Σ μ (C ∷ Δ)} (p : Γ ≃ [ ⊥ ] + Δ) → Delayed (wait (ch ⟨ > p ⟩ P))
  case     : ∀{Γ Δ C A B μ} {P : Proc Σ μ (A ∷ C ∷ Δ)} {Q : Proc Σ μ (B ∷ C ∷ Δ)} (p : Γ ≃ [ A & B ] + Δ) → Delayed (case (ch ⟨ > p ⟩ (P , Q)))
  select-l : ∀{Γ Δ C A B μ} {P : Proc Σ μ (A ∷ C ∷ Δ)} (p : Γ ≃ [ A ⊕ B ] + Δ) → Delayed (select (ch ⟨ > p ⟩ inj₁ P))
  select-r : ∀{Γ Δ C A B μ} {P : Proc Σ μ (B ∷ C ∷ Δ)} (p : Γ ≃ [ A ⊕ B ] + Δ) → Delayed (select (ch ⟨ > p ⟩ inj₂ P))
  join     : ∀{Γ Δ C A B μ} {P : Proc Σ μ (A ∷ B ∷ C ∷ Δ)} (p : Γ ≃ [ A ⅋ B ] + Δ) → Delayed (join (ch ⟨ > p ⟩ P))
  fork-l   : ∀{Γ Δ Δ₁ Δ₂ C A B μ ν} {P : Proc Σ μ (A ∷ C ∷ Δ₁)} {Q : Proc Σ ν (B ∷ Δ₂)}
             (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) → Delayed (fork (ch ⟨ > p ⟩ (P ⟨ < q ⟩ Q)))
  fork-r   : ∀{Γ Δ Δ₁ Δ₂ C A B μ ν} {P : Proc Σ μ (A ∷ Δ₁)} {Q : Proc Σ ν (B ∷ C ∷ Δ₂)}
             (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) → Delayed (fork (ch ⟨ > p ⟩ (P ⟨ > q ⟩ Q)))
  put      : ∀{Γ Δ C A μ ω} {P : Proc Σ μ (A ∷ C ∷ Δ)} (p : Γ ≃ [ put ω ⨟ A ] + Δ) → Delayed (put (ch ⟨ > p ⟩ P))
  get      : ∀{Γ Δ C A μ ν ω} {P : Proc Σ μ (A ∷ C ∷ Δ)} (eq : μ ≡ ν + ω) (p : Γ ≃ [ get ω ⨟ A ] + Δ) → Delayed (get eq (ch ⟨ > p ⟩ P))

data Thread {n Σ μ Γ} (P : Proc {n} Σ μ Γ) : Set where
  link    : Link P → Thread P
  delayed : Delayed P → Thread P
  output  : Output P → Thread P
  input   : Input P → Thread P

Observable : ∀{n Σ μ Γ} → Proc {n} Σ μ Γ → Set
Observable {_} {Σ} {_} {Γ} P = ∃[ ν ] Σ[ Q ∈ Proc Σ ν Γ ] P ⊒ Q × Thread Q

Reducible : ∀{n Σ μ Γ} → Def Σ → Proc {n} Σ μ Γ → Set
Reducible {_} {Σ} ℙ P = ∃[ ν ] ∃[ Δ ] Σ[ Q ∈ Proc Σ ν Δ ] (ℙ ⊢ P ↝ Q)

Alive : ∀{n Σ μ Γ} → Def Σ → Proc {n} Σ μ Γ → Set
Alive ℙ P = Observable P ⊎ Reducible ℙ P

fail→thread : ∀{n Σ μ Γ Δ} (p : Γ ≃ [ ⊤ ] + Δ) → Thread {n} {Σ} (fail {μ = μ} (ch ⟨ p ⟩ tt))
fail→thread (< p) = input (fail p)
fail→thread (> p) = delayed (fail p)

wait→thread : ∀{n Σ μ Γ Δ} {P : Proc Σ μ Δ} (p : Γ ≃ [ ⊥ ] + Δ) → Thread {n} {Σ} (wait (ch ⟨ p ⟩ P))
wait→thread (< p) = input (wait p)
wait→thread (> p) = delayed (wait p)

case→thread : ∀{n Σ A B μ Γ Δ} {P : Proc Σ μ (A ∷ Δ)} {Q : Proc Σ μ (B ∷ Δ)} (p : Γ ≃ [ A & B ] + Δ) → Thread {n} {Σ} (case (ch ⟨ p ⟩ (P , Q)))
case→thread (< p) = input (case p)
case→thread (> p) = delayed (case p)

left→thread : ∀{n Σ A B μ Γ Δ} {P : Proc Σ μ (A ∷ Δ)} (p : Γ ≃ [ A ⊕ B ] + Δ) → Thread {n} {Σ} (select (ch ⟨ p ⟩ inj₁ P))
left→thread (< p) = output (select-l p)
left→thread (> p) = delayed (select-l p)

right→thread : ∀{n Σ A B μ Γ Δ} {P : Proc Σ μ (B ∷ Δ)} (p : Γ ≃ [ A ⊕ B ] + Δ) → Thread {n} {Σ} (select (ch ⟨ p ⟩ inj₂ P))
right→thread (< p) = output (select-r p)
right→thread (> p) = delayed (select-r p)

join→thread : ∀{n Σ A B μ Γ Δ} {P : Proc Σ μ (A ∷ B ∷ Δ)} (p : Γ ≃ [ A ⅋ B ] + Δ) → Thread {n} {Σ} (join (ch ⟨ p ⟩ P))
join→thread (< p) = input (join p)
join→thread (> p) = delayed (join p)

fork→thread : ∀{n Σ A B μ ν Γ Δ Δ₁ Δ₂} {P : Proc Σ μ (A ∷ Δ₁)} {Q : Proc Σ ν (B ∷ Δ₂)} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) → Thread {n} {Σ} (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q)))
fork→thread (< p) q = output (fork p q)
fork→thread (> p) (< q) = delayed (fork-l p q)
fork→thread (> p) (> q) = delayed (fork-r p q)

put→thread : ∀{n Σ A μ ω Γ Δ} {P : Proc Σ μ (A ∷ Δ)} (p : Γ ≃ [ put ω ⨟ A ] + Δ) → Thread {n} {Σ} (put (ch ⟨ p ⟩ P))
put→thread (< p) = output (put p)
put→thread (> p) = delayed (put p)

get→thread : ∀{n Σ A μ ν ω Γ Δ} {P : Proc Σ μ (A ∷ Δ)} (eq : μ ≡ ν + ω) (p : Γ ≃ [ get ω ⨟ A ] + Δ) → Thread {n} {Σ} (get eq (ch ⟨ p ⟩ P))
get→thread eq (< p) = input (get eq p)
get→thread eq (> p) = delayed (get eq p)

data CanonicalCut {n Σ Γ} : ∀{μ} → Proc {n} Σ μ Γ → Set where
  cc-link    : ∀{Γ₁ Γ₂ A B μ ν} {P : Proc Σ μ (A ∷ Γ₁)} {Q : Proc Σ ν (B ∷ Γ₂)}
               (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
               Link P → CanonicalCut (cut eq (P ⟨ p ⟩ Q))
  cc-redex   : ∀{Γ₁ Γ₂ A B μ ν} {P : Proc Σ μ (A ∷ Γ₁)} {Q : Proc Σ ν (B ∷ Γ₂)}
               (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
               Input P → Output Q → CanonicalCut (cut eq (P ⟨ p ⟩ Q))
  cc-delayed : ∀{Γ₁ Γ₂ A B μ ν} {P : Proc Σ μ (A ∷ Γ₁)} {Q : Proc Σ ν (B ∷ Γ₂)}
               (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
               Delayed P → CanonicalCut (cut eq (P ⟨ p ⟩ Q))

output-output : ∀{n Σ A B μ ν Γ Δ} {P : Proc {n} Σ μ (A ∷ Γ)} {Q : Proc Σ ν (B ∷ Δ)} → dual A ≈ B → ¬ (Output P × Output Q)
output-output eq (close , close) = not≈ sim⊥𝟙 eq
output-output eq (close , select-l p) = not≈ sim⊥⊕ eq
output-output eq (close , select-r p) = not≈ sim⊥⊕ eq
output-output eq (close , fork p q) = not≈ sim⊥⊗ eq
output-output eq (select-l p , close) = not≈ sim⊥⊕ (≈sym (≈dual eq))
output-output eq (select-l p , select-l _) = not≈ sim&⊕ eq
output-output eq (select-l p , select-r _) = not≈ sim&⊕ eq
output-output eq (select-l p , fork _ q) = not≈ sim&⊗ eq
output-output eq (select-r p , close) = not≈ sim⊥⊕ (≈sym (≈dual eq))
output-output eq (select-r p , select-l _) = not≈ sim&⊕ eq
output-output eq (select-r p , select-r _) = not≈ sim&⊕ eq
output-output eq (select-r p , fork _ q) = not≈ sim&⊗ eq
output-output eq (fork p q , close) = not≈ sim⊥⊗ (≈sym (≈dual eq))
output-output eq (fork p q , select-l _) = not≈ sim&⊗ (≈sym (≈dual eq))
output-output eq (fork p q , select-r _) = not≈ sim&⊗ (≈sym (≈dual eq))
output-output eq (fork p q , fork _ _) = not≈ sim⅋⊗ eq
output-output eq (close , put _) = not≈ sim⊥put eq
output-output eq (select-l p , put _) = not≈ sim&put eq
output-output eq (select-r p , put _) = not≈ sim&put eq
output-output eq (fork p q , put _) = not≈ sim⅋put eq
output-output eq (put p , close) = not≈ sim⊥put (≈sym (≈dual eq))
output-output eq (put p , select-l _) = not≈ sim&put (≈sym (≈dual eq))
output-output eq (put p , select-r _) = not≈ sim&put (≈sym (≈dual eq))
output-output eq (put p , fork _ q) = not≈ sim⅋put (≈sym (≈dual eq))
output-output eq (put p , put _) = not≈ simgetput eq

input-input : ∀{n Σ A B μ ν Γ Δ} {P : Proc {n} Σ μ (A ∷ Γ)} {Q : Proc Σ ν (B ∷ Δ)} → dual A ≈ B → ¬ (Input P × Input Q)
input-input eq (fail p , fail _) = not≈ sim⊤𝟘 (≈dual eq)
input-input eq (fail p , wait _) = not≈ sim⊤𝟙 (≈dual eq)
input-input eq (fail p , case _) = not≈ sim⊤⊕ (≈dual eq)
input-input eq (fail p , join _) = not≈ sim⊤⊗ (≈dual eq)
input-input eq (wait p , fail _) = not≈ sim⊤𝟙 (≈sym eq)
input-input eq (wait p , wait _) = not≈ sim⊥𝟙 (≈sym eq)
input-input eq (wait p , case _) = not≈ sim⊥⊕ (≈dual eq)
input-input eq (wait p , join _) = not≈ sim⊥⊗ (≈dual eq)
input-input eq (case p , fail _) = not≈ sim⊤⊕ (≈sym eq)
input-input eq (case p , wait _) = not≈ sim⊥⊕ (≈sym eq)
input-input eq (case p , case _) = not≈ sim&⊕ (≈sym eq)
input-input eq (case p , join _) = not≈ sim&⊗ (≈dual eq)
input-input eq (join p , fail _) = not≈ sim⊤⊗ (≈sym eq)
input-input eq (join p , wait _) = not≈ sim⊥⊗ (≈sym eq)
input-input eq (join p , case _) = not≈ sim&⊗ (≈sym eq)
input-input eq (join p , join _) = not≈ sim⅋⊗ (≈sym eq)
input-input eq (fail p , get eq₁ _) = not≈ sim⊤put (≈dual eq)
input-input eq (wait p , get eq₁ _) = not≈ sim⊥put (≈dual eq)
input-input eq (case p , get eq₁ _) = not≈ sim&put (≈dual eq)
input-input eq (join p , get eq₁ _) = not≈ sim⅋put (≈dual eq)
input-input eq (get eq₁ p , fail _) = not≈ sim⊤put (≈sym eq)
input-input eq (get eq₁ p , wait _) = not≈ sim⊥put (≈sym eq)
input-input eq (get eq₁ p , case _) = not≈ sim&put (≈sym eq)
input-input eq (get eq₁ p , join _) = not≈ sim⅋put (≈sym eq)
input-input eq (get eq₁ p , get eq₂ _) = not≈ simgetput (≈sym eq)

canonical-cut : ∀{n Σ A B μ ν Γ Γ₁ Γ₂} {P : Proc Σ μ (A ∷ Γ₁)} {Q : Proc Σ ν (B ∷ Γ₂)}
                (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
                Thread {n} {Σ} P → Thread Q →
                ∃[ ω ] Σ[ R ∈ Proc Σ ω Γ ] CanonicalCut R × cut {A = A} eq (P ⟨ p ⟩ Q) ⊒ R
canonical-cut eq pc (link x) Qt = _ , _ , cc-link eq pc x , s-refl
canonical-cut eq pc Pt (link y) = _ , _ , cc-link (≈sym (≈dual eq)) (+-comm pc) y , s-comm eq pc
canonical-cut eq pc (delayed x) Qt = _ , _ , cc-delayed eq pc x , s-refl
canonical-cut eq pc Pt (delayed y) = _ , _ , cc-delayed (≈sym (≈dual eq)) (+-comm pc) y , s-comm eq pc
canonical-cut eq pc (output x) (output y) = contradiction (x , y) (output-output eq)
canonical-cut eq pc (output x) (input y) = _ , _ , cc-redex (≈sym (≈dual eq)) (+-comm pc) y x , s-comm eq pc
canonical-cut eq pc (input x) (output y) = _ , _ , cc-redex eq pc x y , s-refl
canonical-cut eq pc (input x) (input y) = contradiction (x , y) (input-input eq)

⊒Alive : ∀{n Σ μ ν Γ} {P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Γ} (ℙ : Def Σ) → P ⊒ Q → Alive ℙ Q → Alive ℙ P
⊒Alive ℙ pcong (inj₁ (_ , _ , x , th)) = inj₁ (_ , _ , s-tran pcong x , th)
⊒Alive ℙ pcong (inj₂ (_ , Δ , Q , red)) = inj₂ (_ , Δ , Q , r-cong pcong red)

canonical-cut-alive : ∀{n Σ μ Γ} {C : Proc {n} Σ μ Γ} (ℙ : Def Σ) → CanonicalCut C → Alive ℙ C
canonical-cut-alive ℙ (cc-link eq pc (link eq' (< > •))) =
  inj₂ (_ , _ , _ , r-link eq eq' pc)
canonical-cut-alive ℙ (cc-link eq pc (link eq' (> < •))) =
  inj₂ (_ , _ , _ , r-cong (s-cong eq pc (s-link eq' _) s-refl) (r-link eq (≈sym (≈dual eq')) pc))
canonical-cut-alive ℙ (cc-redex eq p (fail _) close) = contradiction eq (not≈ sim𝟘𝟙)
canonical-cut-alive ℙ (cc-redex eq p (fail _) (select-l _)) = contradiction (≈dual eq) (not≈ sim⊤&)
canonical-cut-alive ℙ (cc-redex eq p (fail _) (select-r _)) = contradiction (≈dual eq) (not≈ sim⊤&)
canonical-cut-alive ℙ (cc-redex eq p (fail _) (fork _ _)) = contradiction (≈dual eq) (not≈ sim⊤⅋)
canonical-cut-alive ℙ (cc-redex eq p (fail _) (put _)) = contradiction (≈dual eq) (not≈ sim⊤get)
canonical-cut-alive ℙ (cc-redex eq pc (wait p) close) with +-empty-l p | +-empty-l (+-comm pc)
... | refl | refl = inj₂ (_ , _ , _ , r-close eq pc p)
canonical-cut-alive ℙ (cc-redex eq p (wait _) (select-l _)) = contradiction eq (not≈ sim𝟙⊕)
canonical-cut-alive ℙ (cc-redex eq p (wait _) (select-r _)) = contradiction eq (not≈ sim𝟙⊕)
canonical-cut-alive ℙ (cc-redex eq p (wait _) (fork _ _)) = contradiction eq (not≈ sim𝟙⊗)
canonical-cut-alive ℙ (cc-redex eq p (wait _) (put _)) = contradiction eq (not≈ sim𝟙put)
canonical-cut-alive ℙ (cc-redex eq p (case _) close) = contradiction (≈sym eq) (not≈ sim𝟙⊕)
canonical-cut-alive ℙ (cc-redex eq pc (case p) (select-l q)) with +-empty-l p | +-empty-l q
... | refl | refl = inj₂ (_ , _ , _ , r-select-l eq pc p q)
canonical-cut-alive ℙ (cc-redex eq pc (case p) (select-r q)) with +-empty-l p | +-empty-l q
... | refl | refl = inj₂ (_ , _ , _ , r-select-r eq pc p q)
canonical-cut-alive ℙ (cc-redex eq p (case _) (fork _ _)) = contradiction eq (not≈ sim⊕⊗)
canonical-cut-alive ℙ (cc-redex eq p (case _) (put _)) = contradiction eq (not≈ sim⊕put)
canonical-cut-alive ℙ (cc-redex eq p (join _) close) = contradiction (≈sym eq) (not≈ sim𝟙⊗)
canonical-cut-alive ℙ (cc-redex eq p (join _) (select-l _)) = contradiction (≈sym eq) (not≈ sim⊕⊗)
canonical-cut-alive ℙ (cc-redex eq p (join _) (select-r _)) = contradiction (≈sym eq) (not≈ sim⊕⊗)
canonical-cut-alive ℙ (cc-redex eq pc (join p) (fork q r)) with +-empty-l p | +-empty-l q
... | refl | refl = inj₂ (_ , _ , _ , r-fork eq pc p r q)
canonical-cut-alive ℙ (cc-redex eq p (join _) (put _)) = contradiction eq (not≈ sim⊗put)
canonical-cut-alive ℙ (cc-redex eq p (get _ _) close) = contradiction (≈sym eq) (not≈ sim𝟙put)
canonical-cut-alive ℙ (cc-redex eq p (get _ _) (select-l _)) = contradiction (≈sym eq) (not≈ sim⊕put)
canonical-cut-alive ℙ (cc-redex eq p (get _ _) (select-r _)) = contradiction (≈sym eq) (not≈ sim⊕put)
canonical-cut-alive ℙ (cc-redex eq p (get _ _) (fork _ q)) = contradiction (≈sym eq) (not≈ sim⊗put)
canonical-cut-alive ℙ (cc-redex eq pc (get eq' p) (put q)) with +-empty-l p | +-empty-l q | ≈measure eq
... | refl | refl | refl = inj₂ (_ , _ , _ , r-put eq eq' pc p q)
canonical-cut-alive ℙ (cc-delayed eq p (fail q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , _ , s-fail eq p q , fail→thread q')
canonical-cut-alive ℙ (cc-delayed eq p (wait q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , _ , s-wait eq p q , wait→thread q')
canonical-cut-alive ℙ (cc-delayed eq p (case q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , _ , s-case eq p q , case→thread q')
canonical-cut-alive ℙ (cc-delayed eq p (select-l q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , _ , s-select-l eq p q , left→thread q')
canonical-cut-alive ℙ (cc-delayed eq p (select-r q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , _ , s-select-r eq p q , right→thread q')
canonical-cut-alive ℙ (cc-delayed eq p (join q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , _ , s-join eq p q , join→thread q')
canonical-cut-alive ℙ (cc-delayed eq p (fork-l q r)) =
  let _ , p' , q' = +-assoc-l p q in
  let _ , p'' , r' = +-assoc-l p' r in
  let _ , q'' , r'' = +-assoc-r r' (+-comm p'') in
  inj₁ (_ , _ , s-fork-l eq p q r , fork→thread q' r'')
canonical-cut-alive ℙ (cc-delayed eq p (fork-r q r)) =
  let _ , p' , q' = +-assoc-l p q in
  let _ , p'' , r' = +-assoc-l p' r in
  inj₁ (_ , _ , s-fork-r eq p q r , fork→thread q' r')
canonical-cut-alive ℙ (cc-delayed eq p (put q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , _ , s-put eq p q , put→thread q')
canonical-cut-alive ℙ (cc-delayed {μ = μ₁} {μ₂} eq p (get {μ = μ} {ν} {ω} eq' q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , _ , s-get eq eq' p q , get→thread (ugly-assoc μ μ₂ μ₁ ω eq') q')

deadlock-freedom : ∀{n Σ μ Γ} (ℙ : Def Σ) (P : Proc {n} Σ μ Γ) → Alive ℙ P
deadlock-freedom ℙ (call x cσ π) = inj₂ (_ , _ , _ , r-call x cσ π)
deadlock-freedom ℙ (link eq (ch ⟨ p ⟩ ch)) = inj₁ (_ , _ , s-refl , link (link eq p))
deadlock-freedom ℙ (fail (ch ⟨ p ⟩ _)) = inj₁ (_ , _ , s-refl , fail→thread p)
deadlock-freedom ℙ (wait (ch ⟨ p ⟩ _)) = inj₁ (_ , _ , s-refl , wait→thread p)
deadlock-freedom ℙ (close ch) = inj₁ (_ , _ , s-refl , output close)
deadlock-freedom ℙ (case (ch ⟨ p ⟩ _)) = inj₁ (_ , _ , s-refl , case→thread p)
deadlock-freedom ℙ (select (ch ⟨ p ⟩ inj₁ _)) = inj₁ (_ , _ , s-refl , left→thread p)
deadlock-freedom ℙ (select (ch ⟨ p ⟩ inj₂ _)) = inj₁ (_ , _ , s-refl , right→thread p)
deadlock-freedom ℙ (join (ch ⟨ p ⟩ _)) = inj₁ (_ , _ , s-refl , join→thread p)
deadlock-freedom ℙ (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) = inj₁ (_ , _ , s-refl , fork→thread p q)
deadlock-freedom ℙ (put (ch ⟨ p ⟩ _)) = inj₁ (_ , _ , s-refl , put→thread p)
deadlock-freedom ℙ (get eq (ch ⟨ p ⟩ _)) = inj₁ (_ , _ , s-refl , get→thread eq p)
deadlock-freedom ℙ (cut eq (P ⟨ p ⟩ R)) with deadlock-freedom ℙ P
deadlock-freedom ℙ (cut eq (P ⟨ p ⟩ R)) | inj₂ (_ , _ , Q , red) with ↝≈ red
... | eqA ∷ eqC = inj₂ (_ , _ , _ , r-cut eq eqA eqC p red)
deadlock-freedom ℙ (cut eq (P ⟨ p ⟩ Q)) | inj₁ (_ , Pc , Pt) with deadlock-freedom ℙ Q
deadlock-freedom ℙ (cut eq (P ⟨ p ⟩ Q)) | inj₁ (_ , Pc , Pt) | inj₂ (_ , _ , Q' , red) with ↝≈ red
... | eqB ∷ eqC = inj₂ (_ , _ , _ , r-cong (s-comm eq p) (r-cut (≈sym (≈dual eq)) eqB eqC (+-comm p) red))
deadlock-freedom ℙ (cut eq (P ⟨ p ⟩ Q)) | inj₁ (_ , _ , Pc , Pt) | inj₁ (_ , _ , Qc , Qt) with canonical-cut eq p Pt Qt
... | _ , _ , cc , pcong = ⊒Alive ℙ (s-tran (s-cong eq p Pc Qc) pcong) (canonical-cut-alive ℙ cc)
