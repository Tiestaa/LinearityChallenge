{-# OPTIONS --rewriting #-}
open import Data.Unit using (tt)
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (refl)

open import Type
open import Context
open import Process
open import Reduction
open import Congruence

data Link : ∀{Γ} → Proc Γ → Set where
  link : ∀{Γ A} (p : Γ ≃ [ A ] + [ dual A ]) → Link (link (ch ⟨ p ⟩ ch))

data Input : ∀{Γ} → Proc Γ → Set where
  fail : ∀{Γ Δ} (p : Γ ≃ [] + Δ) → Input (fail (ch ⟨ < p ⟩ tt))
  wait : ∀{Γ Δ P} (p : Γ ≃ [] + Δ) → Input (wait (ch ⟨ < p ⟩ P))
  case : ∀{Γ Δ A B P Q} (p : Γ ≃ [] + Δ) → Input (case {A} {B} (ch ⟨ < p ⟩ (P , Q)))
  join : ∀{Γ Δ A B P} (p : Γ ≃ [] + Δ) → Input (join {A} {B} (ch ⟨ < p ⟩ P))

data Output : ∀{Γ} → Proc Γ → Set where
  close    : Output (close ch)
  select-l : ∀{Γ Δ A B P} (p : Γ ≃ [] + Δ) → Output (select {A} {B} (ch ⟨ < p ⟩ inj₁ P))
  select-r : ∀{Γ Δ A B P} (p : Γ ≃ [] + Δ) → Output (select {A} {B} (ch ⟨ < p ⟩ inj₂ P))
  fork     : ∀{Γ Δ Δ₁ Δ₂ A B P Q} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂) → Output (fork {A} {B} (ch ⟨ < p ⟩ (P ⟨ q ⟩ Q)))

data Delayed : ∀{Γ} → Proc Γ → Set where
  fail     : ∀{C Γ Δ} (p : Γ ≃ [ ⊤ ] + Δ) → Delayed (fail (ch ⟨ >_ {C} p ⟩ tt))
  wait     : ∀{C Γ Δ P} (p : Γ ≃ [ ⊥ ] + Δ) → Delayed (wait (ch ⟨ >_ {C} p ⟩ P))
  case     : ∀{Γ Δ C A B P} (p : Γ ≃ [ A & B ] + Δ) → Delayed (case {A} {B} (ch ⟨ >_ {C} p ⟩ P))
  select-l : ∀{Γ Δ C A B P} (p : Γ ≃ [ A ⊕ B ] + Δ) → Delayed (select (ch ⟨ >_ {C} p ⟩ inj₁ P))
  select-r : ∀{Γ Δ C A B P} (p : Γ ≃ [ A ⊕ B ] + Δ) → Delayed (select (ch ⟨ >_ {C} p ⟩ inj₂ P))
  join     : ∀{Γ Δ C A B P} (p : Γ ≃ [ A ⅋ B ] + Δ) → Delayed (join (ch ⟨ >_ {C} p ⟩ P))
  fork-l   : ∀{Γ Δ Δ₁ Δ₂ C A B P Q} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) →
             Delayed (fork (ch ⟨ >_ {C} p ⟩ (P ⟨ < q ⟩ Q)))
  fork-r   : ∀{Γ Δ Δ₁ Δ₂ C A B P Q} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) →
             Delayed (fork (ch ⟨ >_ {C} p ⟩ (P ⟨ > q ⟩ Q)))

data Server : ∀{Γ} → Proc Γ → Set where

data DelayedServer : ∀{Γ} → Proc Γ → Set where

data Thread {Γ} (P : Proc Γ) : Set where
  link    : Link P → Thread P
  delayed : Delayed P → Thread P
  output  : Output P → Thread P
  input   : Input P → Thread P
  server  : Server P → Thread P
  dserver : DelayedServer P → Thread P

Observable : ∀{Γ} → Proc Γ → Set
Observable P = ∃[ Q ] P ⊒ Q × Thread Q

Reducible : ∀{Γ} → Proc Γ → Set
Reducible P = ∃[ Q ] P ↝ Q

Alive : ∀{Γ} → Proc Γ → Set
Alive P = Observable P ⊎ Reducible P

fail→thread : ∀{Γ Δ} (p : Γ ≃ [ ⊤ ] + Δ) → Thread (fail (ch ⟨ p ⟩ tt))
fail→thread (< p) = input (fail p)
fail→thread (> p) = delayed (fail p)

wait→thread : ∀{Γ Δ P} (p : Γ ≃ [ ⊥ ] + Δ) → Thread (wait (ch ⟨ p ⟩ P))
wait→thread (< p) = input (wait p)
wait→thread (> p) = delayed (wait p)

case→thread : ∀{A B Γ Δ P} (p : Γ ≃ [ A & B ] + Δ) → Thread (case (ch ⟨ p ⟩ P))
case→thread (< p) = input (case p)
case→thread (> p) = delayed (case p)

left→thread : ∀{A B Γ Δ P} (p : Γ ≃ [ A ⊕ B ] + Δ) → Thread (select (ch ⟨ p ⟩ inj₁ P))
left→thread (< p) = output (select-l p)
left→thread (> p) = delayed (select-l p)

right→thread : ∀{A B Γ Δ P} (p : Γ ≃ [ A ⊕ B ] + Δ) → Thread (select (ch ⟨ p ⟩ inj₂ P))
right→thread (< p) = output (select-r p)
right→thread (> p) = delayed (select-r p)

join→thread : ∀{A B Γ Δ P} (p : Γ ≃ [ A ⅋ B ] + Δ) → Thread (join (ch ⟨ p ⟩ P))
join→thread (< p) = input (join p)
join→thread (> p) = delayed (join p)

fork→thread : ∀{A B Γ Δ Δ₁ Δ₂ P Q} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) → Thread (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q)))
fork→thread (< p) q = output (fork p q)
fork→thread (> p) (< q) = delayed (fork-l p q)
fork→thread (> p) (> q) = delayed (fork-r p q)

data CanonicalCut {Γ} : Proc Γ → Set where
  cc-link    : ∀{Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) →
               Link P → CanonicalCut (cut {A} (P ⟨ p ⟩ Q))
  cc-redex   : ∀{Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) →
               Output P → (Input ∪ Server) Q → CanonicalCut (cut {A} (P ⟨ p ⟩ Q))
  cc-delayed : ∀{Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) →
               Delayed P → CanonicalCut (cut {A} (P ⟨ p ⟩ Q))
  cc-servers : ∀{Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) →
               DelayedServer P → Server Q → CanonicalCut (cut {A} (P ⟨ p ⟩ Q))

output-output : ∀{A Γ Δ P Q} → ¬ (Output {A ∷ Γ} P × Output {dual A ∷ Δ} Q)
output-output (close , ())

output-delayed-server : ∀{A Γ Δ P Q} → ¬ (Output {A ∷ Γ} P × DelayedServer {dual A ∷ Δ} Q)
output-delayed-server (close , ())

input-input : ∀{A Γ Δ P Q} → ¬ (Input {A ∷ Γ} P × Input {dual A ∷ Δ} Q)
input-input (fail _ , ())

input-server : ∀{A Γ Δ P Q} → ¬ (Input {A ∷ Γ} P × Server {dual A ∷ Δ} Q)
input-server (fail _ , ())

input-delayed-server : ∀{A Γ Δ P Q} → ¬ (Input {A ∷ Γ} P × DelayedServer {dual A ∷ Δ} Q)
input-delayed-server (fail _ , ())

canonical-cut : ∀{A Γ Γ₁ Γ₂ P Q} (p : Γ ≃ Γ₁ + Γ₂) →
                Thread P → Thread Q → ∃[ R ] CanonicalCut R × cut {A} (P ⟨ p ⟩ Q) ⊒ R
canonical-cut pc (link x) Qt = _ , cc-link pc x , s-refl
canonical-cut pc Pt (link y) = _ , cc-link (+-comm pc) y , s-comm pc
canonical-cut pc (delayed x) Qt = _ , cc-delayed pc x , s-refl
canonical-cut pc Pt (delayed y) = _ , cc-delayed (+-comm pc) y , s-comm pc
canonical-cut pc (output x) (output y) = contradiction (x , y) output-output
canonical-cut pc (output x) (input y) = _ , cc-redex pc x (inj₁ y) , s-refl
canonical-cut pc (output x) (server y) = _ , cc-redex pc x (inj₂ y) , s-refl
canonical-cut pc (output x) (dserver y) = contradiction (x , y) output-delayed-server
canonical-cut pc (input x) (output y) = _ , cc-redex (+-comm pc) y (inj₁ x) , s-comm pc
canonical-cut pc (input x) (input y) = contradiction (x , y) input-input
canonical-cut pc (input x) (server y) = contradiction (x , y) input-server
canonical-cut pc (input x) (dserver y) = contradiction (x , y) input-delayed-server
canonical-cut pc (server x) (output y) = _ , cc-redex (+-comm pc) y (inj₂ x) , s-comm pc
canonical-cut pc (server x) (input y) = contradiction (y , x) input-server
canonical-cut pc (server x) (dserver y) = _ , cc-servers (+-comm pc) y x , s-comm pc
canonical-cut pc (dserver x) (output y) = contradiction (y , x) output-delayed-server
canonical-cut pc (dserver x) (input y) = contradiction (y , x) input-delayed-server
canonical-cut pc (dserver x) (server y) = _ , cc-servers pc x y , s-refl

⊒Alive : ∀{Γ} {P Q : Proc Γ} → P ⊒ Q → Alive Q → Alive P
⊒Alive pcong (inj₁ (_ , x , th)) = inj₁ (_ , s-tran pcong x , th)
⊒Alive pcong (inj₂ (_ , red)) = inj₂ (_ , r-cong pcong red)

canonical-cut-alive : ∀{Γ} {C : Proc Γ} → CanonicalCut C → Alive C
canonical-cut-alive (cc-link pc (link (< > •))) = inj₂ (_ , r-link pc)
canonical-cut-alive (cc-link pc (link (> < •))) =
  inj₂ (_ , r-cong (s-cong pc (s-link _) s-refl) (r-link pc))
canonical-cut-alive (cc-redex pc close (inj₁ (wait p))) with +-empty-l p | +-empty-l pc
... | refl | refl = inj₂ (_ , r-close pc p)
canonical-cut-alive (cc-redex pc (select-l p) (inj₁ (case q))) with +-empty-l p | +-empty-l q
... | refl | refl = inj₂ (_ , r-select-l pc p q)
canonical-cut-alive (cc-redex pc (select-r p) (inj₁ (case q))) with +-empty-l p | +-empty-l q
... | refl | refl = inj₂ (_ , r-select-r pc p q)
canonical-cut-alive (cc-redex pc (fork p q) (inj₁ (join r))) with +-empty-l p | +-empty-l r
... | refl | refl = inj₂ (_ , r-fork pc r q p)
canonical-cut-alive (cc-delayed pc (fail p)) =
  let _ , _ , p' = +-assoc-l pc p in
  inj₁ (_ , s-fail pc p , fail→thread p')
canonical-cut-alive (cc-delayed pc (wait p)) =
  let _ , _ , p' = +-assoc-l pc p in
  inj₁ (_ , s-wait pc p , wait→thread p')
canonical-cut-alive (cc-delayed pc (case p)) =
  let _ , _ , p' = +-assoc-l pc p in
  inj₁ (_ , s-case pc p , case→thread p')
canonical-cut-alive (cc-delayed pc (join p)) =
  let _ , _ , p' = +-assoc-l pc p in
  inj₁ (_ , s-join pc p , join→thread p')
canonical-cut-alive (cc-delayed pc (select-l p)) =
  let _ , _ , p' = +-assoc-l pc p in
  inj₁ (_ , s-select-l pc p , left→thread p')
canonical-cut-alive (cc-delayed pc (select-r p)) =
  let _ , _ , p' = +-assoc-l pc p in
  inj₁ (_ , s-select-r pc p , right→thread p')
canonical-cut-alive (cc-delayed p (fork-l q r)) =
  let _ , p' , q' = +-assoc-l p q in
  let _ , p'' , r' = +-assoc-l p' r in
  let _ , q'' , r'' = +-assoc-r r' (+-comm p'') in
  inj₁ (_ , s-fork-l p q r , fork→thread q' r'')
canonical-cut-alive (cc-delayed p (fork-r q r)) =
  let _ , p' , q' = +-assoc-l p q in
  let _ , p'' , r' = +-assoc-l p' r in
  inj₁ (_ , s-fork-r p q r , fork→thread q' r')

deadlock-freedom : ∀{Γ} (P : Proc Γ) → Alive P
deadlock-freedom (link (ch ⟨ p ⟩ ch)) = inj₁ (_ , s-refl , link (link p))
deadlock-freedom (fail (ch ⟨ p ⟩ _)) = inj₁ (_ , s-refl , fail→thread p)
deadlock-freedom (wait (ch ⟨ p ⟩ _)) = inj₁ (_ , s-refl , wait→thread p)
deadlock-freedom (close ch) = inj₁ (_ , s-refl , output close)
deadlock-freedom (case (ch ⟨ p ⟩ _)) = inj₁ (_ , s-refl , case→thread p)
deadlock-freedom (select (ch ⟨ p ⟩ inj₁ _)) = inj₁ (_ , s-refl , left→thread p)
deadlock-freedom (select (ch ⟨ p ⟩ inj₂ _)) = inj₁ (_ , s-refl , right→thread p)
deadlock-freedom (join (ch ⟨ p ⟩ _)) = inj₁ (_ , s-refl , join→thread p)
deadlock-freedom (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) = inj₁ (_ , s-refl , fork→thread p q)
deadlock-freedom (cut (P ⟨ p ⟩ Q)) with deadlock-freedom P
... | inj₂ (_ , red) = inj₂ (_ , r-cut p red)
... | inj₁ (_ , Pc , Pt) with deadlock-freedom Q
... | inj₂ (_ , red) = inj₂ (_ , r-cong (s-comm p) (r-cut (+-comm p) red))
... | inj₁ (_ , Qc , Qt) with canonical-cut p Pt Qt
... | _ , cc , pcong = ⊒Alive (s-tran (s-cong p Pc Qc) pcong) (canonical-cut-alive cc)
