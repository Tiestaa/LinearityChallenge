{-# OPTIONS --rewriting --guardedness #-}
module Type.Equivalence where

open import Function using (_∘_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong)

open import Type
open import Type.Unfolding
open import Type.Transitions
open import Type.Substitution

-- SIMULATION

record Sim {n} (A B : Type n) : Set where
  coinductive
  field
    next : ∀{ℓ A'} → A ⊨ ℓ ⇒ A' → ∃[ B' ] (B ⊨ ℓ ⇒ B' × Sim A' B')

sim-refl : ∀{n} {A : Type n} → Sim A A
sim-refl .Sim.next tr = _ , tr , sim-refl

sim-rec-unfold : ∀{n} {A : PreType n (suc zero)} → Sim (rec A) (unfold A)
sim-rec-unfold .Sim.next (rec tr) = _ , tr , sim-refl

sim-unfold-rec : ∀{n} {A : PreType n (suc zero)} → Sim (unfold A) (rec A)
sim-unfold-rec .Sim.next tr = _ , rec tr , sim-refl

sim-⊥⨟A-⊥ : ∀{n} {A : Type n} → Sim (⊥ ⨟ A) ⊥
sim-⊥⨟A-⊥ .Sim.next (seq ⊥ _) = _ , ⊥ , sim-⊥⨟A-⊥

sim-⊥-⊥⨟A : ∀{n} {A : Type n} → Sim ⊥ (⊥ ⨟ A)
sim-⊥-⊥⨟A .Sim.next ⊥ = _ , seq ⊥ (λ ()) , sim-⊥-⊥⨟A

sim-𝟙⨟A-𝟙 : ∀{n} {A : Type n} → Sim (𝟙 ⨟ A) 𝟙
sim-𝟙⨟A-𝟙 .Sim.next (seq 𝟙 _) = _ , 𝟙 , sim-𝟙⨟A-𝟙

sim-𝟙-𝟙⨟A : ∀{n} {A : Type n} → Sim 𝟙 (𝟙 ⨟ A)
sim-𝟙-𝟙⨟A .Sim.next 𝟙 = _ , seq 𝟙 (λ ()) , sim-𝟙-𝟙⨟A

sim-⊤⨟A-⊤ : ∀{n} {A : Type n} → Sim (⊤ ⨟ A) ⊤
sim-⊤⨟A-⊤ .Sim.next (seq ⊤ _) = _ , ⊤ , sim-⊤⨟A-⊤

sim-⊤-⊤⨟A : ∀{n} {A : Type n} → Sim ⊤ (⊤ ⨟ A)
sim-⊤-⊤⨟A .Sim.next ⊤ = _ , seq ⊤ (λ ()) , sim-⊤-⊤⨟A

sim-𝟘⨟A-𝟘 : ∀{n} {A : Type n} → Sim (𝟘 ⨟ A) 𝟘
sim-𝟘⨟A-𝟘 .Sim.next (seq 𝟘 _) = _ , 𝟘 , sim-𝟘⨟A-𝟘

sim-𝟘-𝟘⨟A : ∀{n} {A : Type n} → Sim 𝟘 (𝟘 ⨟ A)
sim-𝟘-𝟘⨟A .Sim.next 𝟘 = _ , seq 𝟘 (λ ()) , sim-𝟘-𝟘⨟A

sim-A-skip⨟A : ∀{n} {A : Type n} → Sim A (skip ⨟ A)
sim-A-skip⨟A .Sim.next tr = _ , seqε skip tr , sim-refl

sim-skip⨟A-A : ∀{n} {A : Type n} → Sim (skip ⨟ A) A
sim-skip⨟A-A .Sim.next (seq skip ns) = contradiction ε ns
sim-skip⨟A-A .Sim.next (seqε skip tr) = _ , tr , sim-refl

sim-A-A⨟skip : ∀{n} {A : Type n} → Sim A (A ⨟ skip)
sim-A-A⨟skip .Sim.next {ℓ} tr with special-decidable ℓ
... | inj₂ ns = _ , seq tr ns , sim-A-A⨟skip
... | inj₁ ⊗L = _ , seq⊗ tr , sim-refl
... | inj₁ ⅋L = _ , seq⅋ tr , sim-refl
... | inj₁ ε with afterεskip tr
... | refl = _ , seqε tr skip , sim-refl

A⨟skip-sim-A : ∀{n} {A : Type n} → Sim (A ⨟ skip) A
A⨟skip-sim-A .Sim.next {ℓ} (seq tr ns) = _ , tr , A⨟skip-sim-A
A⨟skip-sim-A .Sim.next {ℓ} (seqε sk skip) = skip , sk , sim-refl
A⨟skip-sim-A .Sim.next {ℓ} (seq⊗ tr) = _ , tr , sim-refl
A⨟skip-sim-A .Sim.next {ℓ} (seq⅋ tr) = _ , tr , sim-refl

sim-trans : ∀{n} {A B C : Type n} → Sim A B → Sim B C → Sim A C
sim-trans p q .Sim.next tr with p .Sim.next tr
... | _ , tr' , p' with q .Sim.next tr'
... | _ , tr'' , q' = _ , tr'' , sim-trans p' q'

sim-dual : ∀{n} {A B : Type n} → Sim A B → Sim (dual A) (dual B)
sim-dual le .Sim.next tr with le .Sim.next (transition-dual tr)
... | _ , tr' , le' = _ , transition-dual tr' , sim-dual le'

sim-assoc-l : ∀{n} {A B C : Type n} → Sim (A ⨟ (B ⨟ C)) ((A ⨟ B) ⨟ C)
sim-assoc-l .Sim.next (seq tr ns) = _ , seq (seq tr ns) ns , sim-assoc-l
sim-assoc-l .Sim.next (seqε sk (seq tr ns)) = _ , seq (seqε sk tr) ns , sim-refl
sim-assoc-l .Sim.next (seqε sk (seqε sk' tr)) = _ , seqε (seqε sk sk') tr , sim-refl
sim-assoc-l .Sim.next (seqε sk (seq⊗ tr)) = _ , seq⊗ (seqε sk tr) , sim-refl
sim-assoc-l .Sim.next (seqε sk (seq⅋ tr)) = _ , seq⅋ (seqε sk tr) , sim-refl
sim-assoc-l .Sim.next (seq⊗ tr) = _ , seq⊗ (seq⊗ tr) , sim-refl
sim-assoc-l .Sim.next (seq⅋ tr) = _ , seq⅋ (seq⅋ tr) , sim-refl

sim-assoc-r : ∀{n} {A B C : Type n} → Sim ((A ⨟ B) ⨟ C) (A ⨟ (B ⨟ C))
sim-assoc-r .Sim.next (seq (seq tr _) ns) = _ , seq tr ns , sim-assoc-r
sim-assoc-r .Sim.next (seq (seqε sk tr) ns) = _ , seqε sk (seq tr ns) , sim-refl
sim-assoc-r .Sim.next (seq (seq⊗ tr) ns) = contradiction ⊗L ns
sim-assoc-r .Sim.next (seq (seq⅋ tr) ns) = contradiction ⅋L ns
sim-assoc-r .Sim.next (seqε (seqε sk sk') tr) = _ , seqε sk (seqε sk' tr) , sim-refl
sim-assoc-r .Sim.next (seq⊗ (seq tr ns)) = contradiction ⊗L ns
sim-assoc-r .Sim.next (seq⊗ (seqε sk tr)) = _ , seqε sk (seq⊗ tr) , sim-refl
sim-assoc-r .Sim.next (seq⊗ (seq⊗ tr)) = _ , seq⊗ tr , sim-refl
sim-assoc-r .Sim.next (seq⅋ (seq tr ns)) = contradiction ⅋L ns
sim-assoc-r .Sim.next (seq⅋ (seqε sk tr)) = _ , seqε sk (seq⅋ tr) , sim-refl
sim-assoc-r .Sim.next (seq⅋ (seq⅋ tr)) = _ , seq⅋ tr , sim-refl

sim-assoc-⅋r : ∀{n} {A B C : Type n} → Sim ((A ⅋ B) ⨟ C) (A ⅋ (B ⨟ C))
sim-assoc-⅋r .Sim.next (seq ⅋L ns) = contradiction ⅋L ns
sim-assoc-⅋r .Sim.next (seq ⅋R ns) = _ , ⅋R , sim-refl
sim-assoc-⅋r .Sim.next (seq⅋ ⅋L) = _ , ⅋L , sim-refl

sim-assoc-⅋l : ∀{n} {A B C : Type n} → Sim (A ⅋ (B ⨟ C)) ((A ⅋ B) ⨟ C)
sim-assoc-⅋l .Sim.next ⅋L = _ , seq⅋ ⅋L , sim-refl
sim-assoc-⅋l .Sim.next ⅋R = _ , seq ⅋R (λ ()) , sim-refl

sim-assoc-⊗r : ∀{n} {A B C : Type n} → Sim ((A ⊗ B) ⨟ C) (A ⊗ (B ⨟ C))
sim-assoc-⊗r .Sim.next (seq ⊗L ns) = contradiction ⊗L ns
sim-assoc-⊗r .Sim.next (seq ⊗R ns) = _ , ⊗R , sim-refl
sim-assoc-⊗r .Sim.next (seq⊗ ⊗L) = _ , ⊗L , sim-refl

sim-assoc-⊗l : ∀{n} {A B C : Type n} → Sim (A ⊗ (B ⨟ C)) ((A ⊗ B) ⨟ C)
sim-assoc-⊗l .Sim.next ⊗L = _ , seq⊗ ⊗L , sim-refl
sim-assoc-⊗l .Sim.next ⊗R = _ , seq ⊗R (λ ()) , sim-refl

sim-dist-⊕⨟ : ∀{n} {A B C : Type n} → Sim ((A ⊕ B) ⨟ C) ((A ⨟ C) ⊕ (B ⨟ C))
sim-dist-⊕⨟ .Sim.next (seq ⊕L _) = _ , ⊕L , sim-refl
sim-dist-⊕⨟ .Sim.next (seq ⊕R _) = _ , ⊕R , sim-refl

sim-dist-⨟⊕ : ∀{n} {A B C : Type n} → Sim ((A ⨟ C) ⊕ (B ⨟ C)) ((A ⊕ B) ⨟ C)
sim-dist-⨟⊕ .Sim.next ⊕L = _ , seq ⊕L (λ ()) , sim-refl
sim-dist-⨟⊕ .Sim.next ⊕R = _ , seq ⊕R (λ ()) , sim-refl

sim-dist-&⨟ : ∀{n} {A B C : Type n} → Sim ((A & B) ⨟ C) ((A ⨟ C) & (B ⨟ C))
sim-dist-&⨟ .Sim.next (seq &L _) = _ , &L , sim-refl
sim-dist-&⨟ .Sim.next (seq &R _) = _ , &R , sim-refl

sim-dist-⨟& : ∀{n} {A B C : Type n} → Sim ((A ⨟ C) & (B ⨟ C)) ((A & B) ⨟ C)
sim-dist-⨟& .Sim.next &L = _ , seq &L (λ ()) , sim-refl
sim-dist-⨟& .Sim.next &R = _ , seq &R (λ ()) , sim-refl

sim-cong⨟ : ∀{n} {A A' B B' : Type n} → Sim A A' → Sim B B' → Sim (A ⨟ B) (A' ⨟ B')
sim-cong⨟ ale ble .Sim.next (seq tr ns) with ale .Sim.next tr
... | _ , tr' , ale' = _ , seq tr' ns , sim-cong⨟ ale' ble
sim-cong⨟ ale ble .Sim.next (seqε sk tr) with ale .Sim.next sk
... | _ , sk' , _ with afterεskip sk'
... | refl with ble .Sim.next tr
... | _ , tr' , ble' = _ , seqε sk' tr' , ble'
sim-cong⨟ ale ble .Sim.next (seq⊗ tr) with ale .Sim.next tr
... | _ , tr' , ale' = _ , seq⊗ tr' , ale'
sim-cong⨟ ale ble .Sim.next (seq⅋ tr) with ale .Sim.next tr
... | _ , tr' , ale' = _ , seq⅋ tr' , ale'

sim-cong⨟l : ∀{n} {A B C : Type n} → Sim A B → Sim (A ⨟ C) (B ⨟ C)
sim-cong⨟l le .Sim.next (seq tr ns) with le .Sim.next tr
... | _ , tr' , le' = _ , seq tr' ns , sim-cong⨟l le'
sim-cong⨟l le .Sim.next (seqε sk tr) with le .Sim.next sk
... | _ , sk' , _ with afterεskip sk'
... | refl = _ , seqε sk' tr , sim-refl
sim-cong⨟l le .Sim.next (seq⊗ tr) with le .Sim.next tr
... | _ , tr' , le' = _ , seq⊗ tr' , le'
sim-cong⨟l le .Sim.next (seq⅋ tr) with le .Sim.next tr
... | _ , tr' , le' = _ , seq⅋ tr' , le'

sim-after : ∀{n ℓ} {A B A' B' : Type n} → Sim A B → A ⊨ ℓ ⇒ A' → B ⊨ ℓ ⇒ B' → Sim A' B'
sim-after le p q .Sim.next tr with le .Sim.next p
... | _ , q' , le' rewrite deterministic q q' = le' .Sim.next tr

sim⊥𝟙 : ∀{n} → ¬ Sim {n} ⊥ 𝟙
sim⊥𝟙 sim with sim .Sim.next ⊥
... | _ , () , _

sim⊥⊕ : ∀{n A B} → ¬ Sim {n} ⊥ (A ⊕ B)
sim⊥⊕ sim with sim .Sim.next ⊥
... | _ , () , _

sim𝟙⊕ : ∀{n A B} → ¬ Sim {n} 𝟙 (A ⊕ B)
sim𝟙⊕ sim with sim .Sim.next 𝟙
... | _ , () , _

sim𝟙⊗ : ∀{n A B} → ¬ Sim {n} 𝟙 (A ⊗ B)
sim𝟙⊗ sim with sim .Sim.next 𝟙
... | _ , () , _

sim⊥⊗ : ∀{n A B} → ¬ Sim {n} ⊥ (A ⊗ B)
sim⊥⊗ sim with sim .Sim.next ⊥
... | _ , () , _

sim⊥put : ∀{n μ A} → ¬ Sim {n} ⊥ (put μ ⨟ A)
sim⊥put sim with sim .Sim.next ⊥
... | _ , seq () _ , _
... | _ , seqε () _ , _

sim𝟙put : ∀{n μ A} → ¬ Sim {n} 𝟙 (put μ ⨟ A)
sim𝟙put sim with sim .Sim.next 𝟙
... | _ , seq () _ , _
... | _ , seqε () _ , _

sim⊤𝟘 : ∀{n} → ¬ Sim {n} ⊤ 𝟘
sim⊤𝟘 sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤𝟙 : ∀{n} → ¬ Sim {n} ⊤ 𝟙
sim⊤𝟙 sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤put : ∀{n μ A} → ¬ Sim {n} ⊤ (put μ ⨟ A)
sim⊤put sim with sim .Sim.next ⊤
... | _ , seq () _ , _
... | _ , seqε () _ , _

sim⊤get : ∀{n μ A} → ¬ Sim {n} ⊤ (get μ ⨟ A)
sim⊤get sim with sim .Sim.next ⊤
... | _ , seq () _ , _
... | _ , seqε () _ , _

sim𝟘𝟙 : ∀{n} → ¬ Sim {n} 𝟘 𝟙
sim𝟘𝟙 sim with sim .Sim.next 𝟘
... | _ , () , _

sim⊤⊕ : ∀{n A B} → ¬ Sim {n} ⊤ (A ⊕ B)
sim⊤⊕ sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤& : ∀{n A B} → ¬ Sim {n} ⊤ (A & B)
sim⊤& sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤⊗ : ∀{n A B} → ¬ Sim {n} ⊤ (A ⊗ B)
sim⊤⊗ sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤⅋ : ∀{n A B} → ¬ Sim {n} ⊤ (A ⅋ B)
sim⊤⅋ sim with sim .Sim.next ⊤
... | _ , () , _

sim&⊕ : ∀{n A B C D} → ¬ Sim {n} (A & B) (C ⊕ D)
sim&⊕ sim with sim .Sim.next &L
... | _ , () , _

sim&⊗ : ∀{n A B C D} → ¬ Sim {n} (A & B) (C ⊗ D)
sim&⊗ sim with sim .Sim.next &L
... | _ , () , _

sim&put : ∀{n A B μ C} → ¬ Sim {n} (A & B) (put μ ⨟ C)
sim&put sim with sim .Sim.next &L
... | _ , seq () _ , _
... | _ , seqε () _ , _

sim⊕put : ∀{n A B μ C} → ¬ Sim {n} (A ⊕ B) (put μ ⨟ C)
sim⊕put sim with sim .Sim.next ⊕L
... | _ , seq () _ , _
... | _ , seqε () _ , _

sim⅋put : ∀{n A B μ C} → ¬ Sim {n} (A ⅋ B) (put μ ⨟ C)
sim⅋put sim with sim .Sim.next ⅋L
... | _ , seq () _ , _
... | _ , seqε () _ , _

sim⊗put : ∀{n A B μ C} → ¬ Sim {n} (A ⊗ B) (put μ ⨟ C)
sim⊗put sim with sim .Sim.next ⊗L
... | _ , seq () _ , _
... | _ , seqε () _ , _

simgetput : ∀{n A B μ ν} → ¬ Sim {n} (get μ ⨟ A) (put ν ⨟ B)
simgetput sim with sim .Sim.next (seq get λ ())
... | _ , seq () _ , _
... | _ , seqε () _ , _

sim⊕⊗ : ∀{n A B C D} → ¬ Sim {n} (A ⊕ B) (C ⊗ D)
sim⊕⊗ sim with sim .Sim.next ⊕L
... | _ , () , _

sim⅋⊗ : ∀{n A B C D} → ¬ Sim {n} (A ⅋ B) (C ⊗ D)
sim⅋⊗ sim with sim .Sim.next ⅋L
... | _ , () , _

-- HALF EQUIVALENCE

_≲_ : ∀{n} → Type n → Type n → Set
_≲_ {n} A B = ∀{m} (σ : Substitution n m) → Sim (subst σ A) (subst σ B)

≲refl : ∀{n} {A : Type n} → A ≲ A
≲refl _ = sim-refl

≲trans : ∀{n} {A B C : Type n} → A ≲ B → B ≲ C → A ≲ C
≲trans p q σ = sim-trans (p σ) (q σ)

≲dual : ∀{n} {A B : Type n} → A ≲ B → dual A ≲ dual B
≲dual {n} {A} {B} le σ
  rewrite sym (dual-subst σ A) | sym (dual-subst σ B) = sim-dual (le σ)

≲rec-unfold : ∀{n} {A : PreType n (suc zero)} → rec A ≲ unfold A
≲rec-unfold {_} {A} σ rewrite sym (unfold-subst σ A) = sim-rec-unfold

≲unfold-rec : ∀{n} {A : PreType n (suc zero)} → unfold A ≲ rec A
≲unfold-rec {_} {A} σ rewrite sym (unfold-subst σ A) = sim-unfold-rec

≲skip-left : ∀{n} {A : Type n} → A ≲ (skip ⨟ A)
≲skip-left _ .Sim.next tr = _ , seqε skip tr , sim-refl

≲subst : ∀{m n} {A B : Type m} (σ : Substitution m n) →
         A ≲ B → subst σ A ≲ subst σ B
≲subst {A = A} {B} σ le τ rewrite subst-compose σ τ A | subst-compose σ τ B = le (τ · σ)

≲after : ∀{n ℓ} {A A' B B' : Type n} → A ⊨ ℓ ⇒ A' → B ⊨ ℓ ⇒ B' → A ≲ B → A' ≲ B'
≲after x y le σ = sim-after (le σ) (transition-subst σ x) (transition-subst σ y)

-- EQUIVALENCE

record _≈_ {n} (A B : Type n) : Set where
  field
    to   : A ≲ B
    from : B ≲ A

open _≈_ public

≈refl : ∀{n} {A : Type n} → A ≈ A
≈refl .to   _ = sim-refl
≈refl .from _ = sim-refl

≈sym : ∀{n} {A B : Type n} → A ≈ B → B ≈ A
≈sym p .to   = p .from
≈sym p .from = p .to

≈trans : ∀{n} {A B C : Type n} → A ≈ B → B ≈ C → A ≈ C
≈trans p q .to σ   = sim-trans (p .to σ) (q .to σ)
≈trans p q .from σ = sim-trans (q .from σ) (p .from σ)

≈dual : ∀{n} {A B : Type n} → A ≈ B → dual A ≈ dual B
≈dual {A = A} {B} eq .to   = ≲dual {A = A} {B} (eq .to)
≈dual {A = A} {B} eq .from = ≲dual {A = B} {A} (eq .from)

≈subst : ∀{m n} {A B : Type m} (σ : Substitution m n) →
         A ≈ B → subst σ A ≈ subst σ B
≈subst {A = A} {B} σ eq .to   = ≲subst {A = A} {B} σ (eq .to)
≈subst {A = A} {B} σ eq .from = ≲subst {A = B} {A} σ (eq .from)

≈rec : ∀{n} {A : PreType n (suc zero)} → rec A ≈ unfold A
≈rec {_} {A} .to   = ≲rec-unfold {_} {A}
≈rec {_} {A} .from = ≲unfold-rec {_} {A}

≈after : ∀{n ℓ} {A A' B B' : Type n} → A ⊨ ℓ ⇒ A' → B ⊨ ℓ ⇒ B' → A ≈ B → A' ≈ B'
≈after x y eq .to   = ≲after x y (eq .to)
≈after x y eq .from = ≲after y x (eq .from)

void-no-transitions : ∀{n ℓ} {A : Type n} → ¬ void ⊨ ℓ ⇒ A
void-no-transitions (rec tr) = void-no-transitions tr

void⨟A≈void : ∀{n} {A : Type n} → (void ⨟ A) ≈ void
void⨟A≈void .to   σ .Sim.next (seq tr ns) = contradiction tr void-no-transitions
void⨟A≈void .to   σ .Sim.next (seqε sk tr) = contradiction sk void-no-transitions
void⨟A≈void .to   σ .Sim.next (seq⊗ tr) = contradiction tr void-no-transitions
void⨟A≈void .to   σ .Sim.next (seq⅋ tr) = contradiction tr void-no-transitions
void⨟A≈void .from σ .Sim.next tr = contradiction tr void-no-transitions

A≈skip⨟A : ∀{n} {A : Type n} → A ≈ (skip ⨟ A)
A≈skip⨟A .to   _ = sim-A-skip⨟A
A≈skip⨟A .from _ = sim-skip⨟A-A

A≈A⨟skip : ∀{n} {A : Type n} → A ≈ (A ⨟ skip)
A≈A⨟skip .to   _ = sim-A-A⨟skip
A≈A⨟skip .from _ = A⨟skip-sim-A

≈assoc : ∀{n} {A B C : Type n} → (A ⨟ (B ⨟ C)) ≈ ((A ⨟ B) ⨟ C)
≈assoc .to   _ = sim-assoc-l
≈assoc .from _ = sim-assoc-r

≈cong⨟ : ∀{n} {A A' B B' : Type n} → A ≈ A' → B ≈ B' → (A ⨟ B) ≈ (A' ⨟ B')
≈cong⨟ aeq beq .to   σ = sim-cong⨟ (aeq .to σ) (beq .to σ)
≈cong⨟ aeq beq .from σ = sim-cong⨟ (aeq .from σ) (beq .from σ)

≈cong⨟l : ∀{n} {A B C : Type n} → A ≈ B → (A ⨟ C) ≈ (B ⨟ C)
≈cong⨟l eq .to   σ = sim-cong⨟l (eq .to σ)
≈cong⨟l eq .from σ = sim-cong⨟l (eq .from σ)

≈dist⊕ : ∀{n} {A B C : Type n} → ((A ⊕ B) ⨟ C) ≈ ((A ⨟ C) ⊕ (B ⨟ C))
≈dist⊕ .to   _ = sim-dist-⊕⨟
≈dist⊕ .from _ = sim-dist-⨟⊕

≈dist& : ∀{n} {A B C : Type n} → ((A & B) ⨟ C) ≈ ((A ⨟ C) & (B ⨟ C))
≈dist& .to   _ = sim-dist-&⨟
≈dist& .from _ = sim-dist-⨟&

≈⊥ : ∀{n} {A : Type n} → (⊥ ⨟ A) ≈ ⊥
≈⊥ .to   _ = sim-⊥⨟A-⊥
≈⊥ .from _ = sim-⊥-⊥⨟A

≈𝟙 : ∀{n} {A : Type n} → (𝟙 ⨟ A) ≈ 𝟙
≈𝟙 .to   _ = sim-𝟙⨟A-𝟙
≈𝟙 .from _ = sim-𝟙-𝟙⨟A

≈⊤ : ∀{n} {A : Type n} → (⊤ ⨟ A) ≈ ⊤
≈⊤ .to   _ = sim-⊤⨟A-⊤
≈⊤ .from _ = sim-⊤-⊤⨟A

≈𝟘 : ∀{n} {A : Type n} → (𝟘 ⨟ A) ≈ 𝟘
≈𝟘 .to   _ = sim-𝟘⨟A-𝟘
≈𝟘 .from _ = sim-𝟘-𝟘⨟A

≈⅋⨟ : ∀{n} {A B C : Type n} → ((A ⅋ B) ⨟ C) ≈ (A ⅋ (B ⨟ C))
≈⅋⨟ .to   _ = sim-assoc-⅋r
≈⅋⨟ .from _ = sim-assoc-⅋l

≈⊗⨟ : ∀{n} {A B C : Type n} → ((A ⊗ B) ⨟ C) ≈ (A ⊗ (B ⨟ C))
≈⊗⨟ .to   _ = sim-assoc-⊗r
≈⊗⨟ .from _ = sim-assoc-⊗l

not≈ : ∀{n} {A B : Type n} → ¬ Sim {n} (subst skip-subst A) (subst skip-subst B) → ¬ A ≈ B
not≈ nsim eq = contradiction (eq .to skip-subst) nsim

≈measure : ∀{n} {μ ν} {A B : Type n} → (put μ ⨟ A) ≈ (put ν ⨟ B) → μ ≡ ν
≈measure {n} {A} {B} eq with eq .to {n} skip-subst .Sim.next (seq put λ ())
... | _ , seq put _ , _ = refl
