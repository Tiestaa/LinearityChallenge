{-# OPTIONS --rewriting --guardedness #-}
module Type.SimpleKind where

open import Axioms
open import Function using (_∘_)
open import Data.Nat using (ℕ; suc; zero; _≤_; _<_; s≤s; _⊔_; _+_)
open import Data.Nat.Properties as Nat
open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Fin.Properties as Fin
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction; contraposition)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; cong; cong₂)

open import Type
open import Type.Equality
open import Type.Transitions
open import Type.Equivalence
open import Type.Unfolding

transition-rec-subst : ∀{n r s ℓ} (σ : Unfolding n r s) {A B : PreType n r} →
                       A ⊨ ℓ ⇒ B → rec-subst σ A ⊨ ℓ ⇒ rec-subst σ B
transition-rec-subst σ skip = skip
transition-rec-subst σ ⊥ = ⊥
transition-rec-subst σ 𝟙 = 𝟙
transition-rec-subst σ ⊤ = ⊤
transition-rec-subst σ 𝟘 = 𝟘
transition-rec-subst σ &L = &L
transition-rec-subst σ &R = &R
transition-rec-subst σ ⊕L = ⊕L
transition-rec-subst σ ⊕R = ⊕R
transition-rec-subst σ ⅋L = ⅋L
transition-rec-subst σ ⅋R = ⅋R
transition-rec-subst σ ⊗L = ⊗L
transition-rec-subst σ ⊗R = ⊗R
transition-rec-subst σ (seq x ns) = seq (transition-rec-subst σ x) ns
transition-rec-subst σ (seqε x y) = seqε (transition-rec-subst σ x) (transition-rec-subst σ y)
transition-rec-subst σ (seq⊗ x) = seq⊗ (transition-rec-subst σ x)
transition-rec-subst σ (seq⅋ x) = seq⅋ (transition-rec-subst σ x)
transition-rec-subst σ put = put
transition-rec-subst σ get = get
transition-rec-subst σ {rec A} (rec x) with transition-rec-subst σ x
... | y rewrite rec-subst-unfold σ A = rec y

transition-unfold : ∀{n r ℓ} {A B : PreType n (suc r)} →
                    A ⊨ ℓ ⇒ B → unfold A ⊨ ℓ ⇒ rec-subst (s-just (rec A)) B
transition-unfold x = transition-rec-subst (s-just (rec _)) x

data Skip {n r} : PreType n r → Set where
  skip : Skip skip
  var  : ∀{x} → Skip (var x)
  rav  : ∀{x} → Skip (rav x)
  seq  : ∀{A B} → Skip A → Skip B → Skip (A ⨟ B)
  rec  : ∀{A} → Skip A → Skip (rec A)

data Action {n r} : PreType n r → Set where
  bot  : Action ⊥
  one  : Action 𝟙
  top  : Action ⊤
  zero : Action 𝟘
  put  : ∀{μ} → Action (put μ)
  get  : ∀{μ} → Action (get μ)
  seq  : ∀{A B} → Action A → Action (A ⨟ B)
  seqε : ∀{A B} → Skip A → Action B → Action (A ⨟ B)
  par  : ∀{A B} → Action (A ⅋ B)
  ten  : ∀{A B} → Action (A ⊗ B)
  amp  : ∀{A B} → Action (A & B)
  plus : ∀{A B} → Action (A ⊕ B)
  rec  : ∀{A} → Action A → Action (rec A)

Visible : ∀{n r} → PreType n r → Set
Visible A = Skip A ⊎ Action A

skip-not-action : ∀{n r} {A : PreType n r} → Skip A → ¬ Action A
skip-not-action (seq sk sk') (seq act) = skip-not-action sk act
skip-not-action (seq sk sk') (seqε x act) = skip-not-action sk' act
skip-not-action (rec sk) (rec act) = skip-not-action sk act

skip-after-rec-subst : ∀{n r s} {A : PreType n r} {σ : Unfolding n r s} → Skip A → Skip (rec-subst σ A)
skip-after-rec-subst skip = skip
skip-after-rec-subst var = var
skip-after-rec-subst rav = rav
skip-after-rec-subst (seq sk sk') = seq (skip-after-rec-subst sk) (skip-after-rec-subst sk')
skip-after-rec-subst (rec sk) = rec (skip-after-rec-subst sk)

-- DECIDABILITY

Skip-dec : ∀{n r} (A : PreType n r) → Skip A ⊎ ¬ Skip A
Skip-dec (var x) = inj₁ var
Skip-dec (rav x) = inj₁ rav
Skip-dec skip = inj₁ skip
Skip-dec ⊤ = inj₂ λ ()
Skip-dec 𝟘 = inj₂ λ ()
Skip-dec ⊥ = inj₂ λ ()
Skip-dec 𝟙 = inj₂ λ ()
Skip-dec (A ⨟ B) with Skip-dec A | Skip-dec B
... | inj₁ x | inj₁ y = inj₁ (seq x y)
... | inj₁ x | inj₂ ny = inj₂ λ { (seq _ y) → ny y }
... | inj₂ nx | inj₁ _ = inj₂ λ { (seq x _) → nx x }
... | inj₂ nx | inj₂ _ = inj₂ λ { (seq x _) → nx x }
Skip-dec (A & B) = inj₂ λ ()
Skip-dec (A ⊕ B) = inj₂ λ ()
Skip-dec (A ⅋ B) = inj₂ λ ()
Skip-dec (A ⊗ B) = inj₂ λ ()
Skip-dec (get x) = inj₂ λ ()
Skip-dec (put x) = inj₂ λ ()
Skip-dec (inv x) = inj₂ λ ()
Skip-dec (rec A) with Skip-dec A
... | inj₁ x = inj₁ (rec x)
... | inj₂ y = inj₂ λ { (rec x) → y x }

Action-dec : ∀{n r} (A : PreType n r) → Action A ⊎ ¬ Action A
Action-dec (var x) = inj₂ λ ()
Action-dec (rav x) = inj₂ λ ()
Action-dec skip = inj₂ λ ()
Action-dec ⊤ = inj₁ top
Action-dec 𝟘 = inj₁ zero
Action-dec ⊥ = inj₁ bot
Action-dec 𝟙 = inj₁ one
Action-dec (A ⨟ B) with Action-dec A
... | inj₁ x = inj₁ (seq x)
... | inj₂ nx with Action-dec B
... | inj₂ ny = inj₂ λ { (seq x) → nx x ; (seqε _ y) → ny y}
... | inj₁ y with Skip-dec A
... | inj₁ z = inj₁ (seqε z y)
... | inj₂ nz = inj₂ λ { (seq x) → nx x ; (seqε z y) → nz z}
Action-dec (A & B) = inj₁ amp
Action-dec (A ⊕ B) = inj₁ plus
Action-dec (A ⅋ B) = inj₁ par
Action-dec (A ⊗ B) = inj₁ ten
Action-dec (get x) = inj₁ get
Action-dec (put x) = inj₁ put
Action-dec (inv x) = inj₂ λ ()
Action-dec (rec A) with Action-dec A
... | inj₁ act = inj₁ (rec act)
... | inj₂ nact = inj₂ λ { (rec act) → nact act }

Visible-dec : ∀{n r} (A : PreType n r) → Visible A ⊎ ¬ Visible A
Visible-dec A with Skip-dec A
... | inj₁ emp = inj₁ (inj₁ emp)
... | inj₂ ne with Action-dec A
... | inj₁ act = inj₁ (inj₂ act)
... | inj₂ nact = inj₂ λ { (inj₁ emp) → ne emp ; (inj₂ act) → nact act}

-- SOUNDNESS

skip-sound : ∀{r} {A : PreType 0 r} → Skip A → A ⊨ ε ⇒ skip
skip-sound skip = skip
skip-sound (seq x y) = seqε (skip-sound x) (skip-sound y)
skip-sound (rec x) = rec (transition-unfold (skip-sound x))

action-sound : ∀{r} {A : PreType 0 r} → Action A → ∃[ ℓ ] ∃[ B ] ℓ ≢ ε × A ⊨ ℓ ⇒ B
action-sound bot = _ , _ , (λ ()) , ⊥
action-sound one = _ , _ , (λ ()) , 𝟙
action-sound top = _ , _ , (λ ()) , ⊤
action-sound zero = _ , _ , (λ ()) , 𝟘
action-sound put = _ , _ , (λ ()) , put
action-sound get = _ , _ , (λ ()) , get
action-sound (seq x) with action-sound x
... | ℓ , B , ne , y with special-decidable ℓ
... | inj₂ ns = ℓ , _ , ne , seq y ns
action-sound (seq x) | ε , B , ne , y | inj₁ sp = contradiction refl ne
action-sound (seq x) | ⅋L , B , ne , y | inj₁ sp = ⅋L , _ , ne , seq⅋ y
action-sound (seq x) | ⊗L , B , ne , y | inj₁ sp = ⊗L , _ , ne , seq⊗ y
action-sound (seqε x y) with action-sound y
... | ℓ , B , ne , y = ℓ , B , ne , seqε (skip-sound x) y
action-sound par = _ , _ , (λ ()) , ⅋L
action-sound ten = _ , _ , (λ ()) , ⊗L
action-sound amp = _ , _ , (λ ()) , &L
action-sound plus = _ , _ , (λ ()) , ⊕L
action-sound (rec x) with action-sound x
... | ℓ , B , ne , y = ℓ , _ , ne , rec (transition-unfold y)

visible-sound : ∀{r} {A : PreType 0 r} → Visible A → ∃[ ℓ ] ∃[ B ] A ⊨ ℓ ⇒ B
visible-sound (inj₁ x) = ε , skip , skip-sound x
visible-sound (inj₂ x) with action-sound x
... | ℓ , B , _ , tr = ℓ , B , tr

-- COMPLETENESS

skip-rename-suc : ∀{k n r} {A : PreType n (k + r)} → Skip (rename (ext∗ {r} k suc) A) → Skip A
skip-rename-suc {A = var x} emp = var
skip-rename-suc {A = rav x} emp = rav
skip-rename-suc {A = skip} emp = skip
skip-rename-suc {k} {A = A ⨟ B} (seq ea eb) = seq (skip-rename-suc {k} ea) (skip-rename-suc {k} eb)
skip-rename-suc {k} {A = rec A} (rec emp) = rec (skip-rename-suc {suc k} emp)

action-rename-suc : ∀{k n r} {A : PreType n (k + r)} → Action (rename (ext∗ {r} k suc) A) → Action A
action-rename-suc {A = ⊤} act = top
action-rename-suc {A = 𝟘} act = zero
action-rename-suc {A = ⊥} act = bot
action-rename-suc {A = 𝟙} act = one
action-rename-suc {k} {A = A ⨟ B} (seq act) = seq (action-rename-suc {k} act)
action-rename-suc {k} {A = A ⨟ B} (seqε emp act) = seqε (skip-rename-suc {k} emp) (action-rename-suc {k} act)
action-rename-suc {A = A & B} act = amp
action-rename-suc {A = A ⊕ B} act = plus
action-rename-suc {A = A ⅋ B} act = par
action-rename-suc {A = A ⊗ B} act = ten
action-rename-suc {A = get x} act = get
action-rename-suc {A = put x} act = put
action-rename-suc {k} {A = rec A} (rec act) = rec (action-rename-suc {suc k} act)

skip-exts∗-s-just : ∀{k n r} {A : PreType n (suc r)} (x : Fin (suc k + r)) →
                    Skip (exts∗ k (s-just (rec A)) x) → Skip (rec A)
skip-exts∗-s-just {zero} zero emp = emp
skip-exts∗-s-just {suc k} (suc x) emp = skip-exts∗-s-just x (skip-rename-suc {0} emp)

action-exts∗-s-just : ∀{k n r} {A : PreType n (suc r)} (x : Fin (suc k + r)) →
                      Action (exts∗ k (s-just (rec A)) x) → Action (rec A)
action-exts∗-s-just {zero} zero act = act
action-exts∗-s-just {suc k} (suc x) act = action-exts∗-s-just x (action-rename-suc {0} act)

skip-rec-subst : ∀{k n r} {A : PreType n (suc r)} (B : PreType n (suc k + r)) →
                 Skip (rec-subst (exts∗ k (s-just (rec A))) B) → Skip B ⊎ Skip (rec A)
skip-rec-subst (var x) emp = inj₁ var
skip-rec-subst (rav x) emp = inj₁ rav
skip-rec-subst skip emp = inj₁ skip
skip-rec-subst {A = A} (B ⨟ C) (seq eb ec) with skip-rec-subst {A = A} B eb | skip-rec-subst {A = A} C ec
... | inj₁ eb' | inj₁ ec' = inj₁ (seq eb' ec')
... | inj₁ eb' | inj₂ ea = inj₂ ea
... | inj₂ ea | _ = inj₂ ea
skip-rec-subst (inv x) emp = inj₂ (skip-exts∗-s-just x emp)
skip-rec-subst {A = A} (rec B) (rec emp) with skip-rec-subst {A = A} B emp
... | inj₁ x = inj₁ (rec x)
... | inj₂ y = inj₂ y

action-rec-subst : ∀{k n r} {A : PreType n (suc r)} (B : PreType n (suc k + r)) →
                   Action (rec-subst (exts∗ k (s-just (rec A))) B) →
                   Action B ⊎ Action (rec A) ⊎ Skip (rec A)
action-rec-subst ⊤ top = inj₁ top
action-rec-subst 𝟘 zero = inj₁ zero
action-rec-subst ⊥ bot = inj₁ bot
action-rec-subst 𝟙 one = inj₁ one
action-rec-subst {A = A} (B ⨟ C) (seq act) with action-rec-subst {A = A} B act
... | inj₁ x = inj₁ (seq x)
... | inj₂ y = inj₂ y
action-rec-subst {A = A} (B ⨟ C) (seqε sk act) with skip-rec-subst {A = A} B sk | action-rec-subst {A = A} C act
... | inj₁ x | inj₁ y = inj₁ (seqε x y)
... | inj₁ x | inj₂ y = inj₂ y
... | inj₂ x | inj₁ y = inj₂ (inj₂ x)
... | inj₂ x | inj₂ y = inj₂ y
action-rec-subst (B & C) amp = inj₁ amp
action-rec-subst (B ⊕ C) plus = inj₁ plus
action-rec-subst (B ⅋ C) par = inj₁ par
action-rec-subst (B ⊗ C) ten = inj₁ ten
action-rec-subst (get x) get = inj₁ get
action-rec-subst (put x) put = inj₁ put
action-rec-subst (inv x) act = inj₂ (inj₁ (action-exts∗-s-just x act))
action-rec-subst {A = A} (rec B) (rec act) with action-rec-subst {A = A} B act
... | inj₁ x = inj₁ (rec x)
... | inj₂ y = inj₂ y

skip-unfold : ∀{n r} {A : PreType n (suc r)} → Skip (unfold A) → Skip (rec A)
skip-unfold {A = A} emp with skip-rec-subst {A = A} A emp
... | inj₁ ea = rec ea
... | inj₂ ea = ea

action-unfold : ∀{n r} {A : PreType n (suc r)} → Action (unfold A) → Action (rec A)
action-unfold {A = A} act with action-rec-subst {A = A} A act
... | inj₁ x = rec x
... | inj₂ (inj₁ x) = x
... | inj₂ (inj₂ (rec x)) = contradiction act (skip-not-action (skip-after-rec-subst x))

skip-complete : ∀{n r} {A : PreType n r} → A ⊨ ε ⇒ skip → Skip A
skip-complete skip = skip
skip-complete (seqε x y) = seq (skip-complete x) (skip-complete y)
skip-complete (rec x) = skip-unfold (skip-complete x)

action-complete : ∀{n r ℓ} {A B : PreType n r} → ℓ ≢ ε → A ⊨ ℓ ⇒ B → Action A
action-complete ne skip = contradiction refl ne
action-complete ne ⊥ = bot
action-complete ne 𝟙 = one
action-complete ne ⊤ = top
action-complete ne 𝟘 = zero
action-complete ne &L = amp
action-complete ne &R = amp
action-complete ne ⊕L = plus
action-complete ne ⊕R = plus
action-complete ne ⅋L = par
action-complete ne ⅋R = par
action-complete ne ⊗L = ten
action-complete ne ⊗R = ten
action-complete ne (seq x _) = seq (action-complete ne x)
action-complete ne (seqε x y) = seqε (skip-complete x) (action-complete ne y)
action-complete ne (seq⊗ x) = seq (action-complete ne x)
action-complete ne (seq⅋ x) = seq (action-complete ne x)
action-complete ne put = put
action-complete ne get = get
action-complete ne (rec x) = action-unfold (action-complete ne x)

visible-complete : ∀{n r ℓ} {A B : PreType n r} → A ⊨ ℓ ⇒ B → Visible A
visible-complete {ℓ = ℓ} tr with special-decidable ℓ
... | inj₂ ns = inj₂ (action-complete (λ { refl → ns ε }) tr)
... | inj₁ ε = inj₁ (skip-complete (Eq.subst (_ ⊨ _ ⇒_) (afterεskip tr) tr))
... | inj₁ ⊗L = inj₂ (action-complete (λ ()) tr)
... | inj₁ ⅋L = inj₂ (action-complete (λ ()) tr)
