{-# OPTIONS --rewriting --guardedness #-}
module Type.Kind where

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
open import Type.Substitution
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

data Empty {n r} : PreType n r → Set where
  skip : Empty skip
  var  : ∀{x} → Empty (var x)
  rav  : ∀{x} → Empty (rav x)
  seq  : ∀{A B} → Empty A → Empty B → Empty (A ⨟ B)
  rec  : ∀{A} → Empty A → Empty (rec A)

data Action {n r} : PreType n r → Set where
  var  : ∀{x} → Action (var x)
  rav  : ∀{x} → Action (rav x)
  bot  : Action ⊥
  one  : Action 𝟙
  top  : Action ⊤
  zero : Action 𝟘
  put  : ∀{μ} → Action (put μ)
  get  : ∀{μ} → Action (get μ)
  seq  : ∀{A B} → Action A → Action (A ⨟ B)
  seqε : ∀{A B} → Empty A → Action B → Action (A ⨟ B)
  par  : ∀{A B} → Action (A ⅋ B)
  ten  : ∀{A B} → Action (A ⊗ B)
  amp  : ∀{A B} → Action (A & B)
  plus : ∀{A B} → Action (A ⊕ B)
  rec  : ∀{A} → Action A → Action (rec A)

-- Visible : ∀{n r} → PreType n r → Set
-- Visible A = Empty A ⊎ Action A

empty-not-action : ∀{n r} {A : PreType n r} → Empty A → ¬ Action A
empty-not-action var var = {!!}
empty-not-action rav rav = {!!}
empty-not-action (seq sk sk') (seq act) = empty-not-action sk act
empty-not-action (seq sk sk') (seqε x act) = empty-not-action sk' act
empty-not-action (rec sk) (rec act) = empty-not-action sk act

empty-after-rec-subst : ∀{n r s} {A : PreType n r} {σ : Unfolding n r s} → Empty A → Empty (rec-subst σ A)
empty-after-rec-subst skip = skip
empty-after-rec-subst var = var
empty-after-rec-subst rav = rav
empty-after-rec-subst (seq sk sk') = seq (empty-after-rec-subst sk) (empty-after-rec-subst sk')
empty-after-rec-subst (rec sk) = rec (empty-after-rec-subst sk)

-- DECIDABILITY

Empty-dec : ∀{n r} (A : PreType n r) → Empty A ⊎ ¬ Empty A
Empty-dec (var x) = inj₁ var
Empty-dec (rav x) = inj₁ rav
Empty-dec skip = inj₁ skip
Empty-dec ⊤ = inj₂ λ ()
Empty-dec 𝟘 = inj₂ λ ()
Empty-dec ⊥ = inj₂ λ ()
Empty-dec 𝟙 = inj₂ λ ()
Empty-dec (A ⨟ B) with Empty-dec A | Empty-dec B
... | inj₁ x | inj₁ y = inj₁ (seq x y)
... | inj₁ x | inj₂ ny = inj₂ λ { (seq _ y) → ny y }
... | inj₂ nx | inj₁ _ = inj₂ λ { (seq x _) → nx x }
... | inj₂ nx | inj₂ _ = inj₂ λ { (seq x _) → nx x }
Empty-dec (A & B) = inj₂ λ ()
Empty-dec (A ⊕ B) = inj₂ λ ()
Empty-dec (A ⅋ B) = inj₂ λ ()
Empty-dec (A ⊗ B) = inj₂ λ ()
Empty-dec (get x) = inj₂ λ ()
Empty-dec (put x) = inj₂ λ ()
Empty-dec (inv x) = inj₂ λ ()
Empty-dec (rec A) with Empty-dec A
... | inj₁ x = inj₁ (rec x)
... | inj₂ y = inj₂ λ { (rec x) → y x }

Action-dec : ∀{n r} (A : PreType n r) → Action A ⊎ ¬ Action A
Action-dec (var x) = inj₁ var
Action-dec (rav x) = inj₁ rav
Action-dec skip = inj₂ λ ()
Action-dec ⊤ = inj₁ top
Action-dec 𝟘 = inj₁ zero
Action-dec ⊥ = inj₁ bot
Action-dec 𝟙 = inj₁ one
Action-dec (A ⨟ B) with Action-dec A
... | inj₁ x = inj₁ (seq x)
... | inj₂ nx with Action-dec B
... | inj₂ ny = inj₂ λ { (seq x) → nx x ; (seqε _ y) → ny y}
... | inj₁ y with Empty-dec A
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

-- Visible-dec : ∀{n r} (A : PreType n r) → Visible A ⊎ ¬ Visible A
-- Visible-dec A with Empty-dec A
-- ... | inj₁ emp = inj₁ (inj₁ emp)
-- ... | inj₂ ne with Action-dec A
-- ... | inj₁ act = inj₁ (inj₂ act)
-- ... | inj₂ nact = inj₂ λ { (inj₁ emp) → ne emp ; (inj₂ act) → nact act}

-- SOUNDNESS

empty-sound : ∀{r} {A : PreType 0 r} → Empty A → A ⊨ ε ⇒ skip
empty-sound skip = skip
empty-sound (seq x y) = seqε (empty-sound x) (empty-sound y)
empty-sound (rec x) = rec (transition-unfold (empty-sound x))

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
... | ℓ , B , ne , y = ℓ , B , ne , seqε (empty-sound x) y
action-sound par = _ , _ , (λ ()) , ⅋L
action-sound ten = _ , _ , (λ ()) , ⊗L
action-sound amp = _ , _ , (λ ()) , &L
action-sound plus = _ , _ , (λ ()) , ⊕L
action-sound (rec x) with action-sound x
... | ℓ , B , ne , y = ℓ , _ , ne , rec (transition-unfold y)

-- visible-sound : ∀{r} {A : PreType 0 r} → Visible A → ∃[ ℓ ] ∃[ B ] A ⊨ ℓ ⇒ B
-- visible-sound (inj₁ x) = ε , skip , empty-sound x
-- visible-sound (inj₂ x) with action-sound x
-- ... | ℓ , B , _ , tr = ℓ , B , tr

-- COMPLETENESS

empty-rename-suc : ∀{k n r} {A : PreType n (k + r)} → Empty (rename (ext∗ {r} k suc) A) → Empty A
empty-rename-suc {A = var x} emp = var
empty-rename-suc {A = rav x} emp = rav
empty-rename-suc {A = skip} emp = skip
empty-rename-suc {k} {A = A ⨟ B} (seq ea eb) = seq (empty-rename-suc {k} ea) (empty-rename-suc {k} eb)
empty-rename-suc {k} {A = rec A} (rec emp) = rec (empty-rename-suc {suc k} emp)

action-rename-suc : ∀{k n r} {A : PreType n (k + r)} → Action (rename (ext∗ {r} k suc) A) → Action A
action-rename-suc {A = var _} act = var
action-rename-suc {A = rav _} act = rav
action-rename-suc {A = ⊤} act = top
action-rename-suc {A = 𝟘} act = zero
action-rename-suc {A = ⊥} act = bot
action-rename-suc {A = 𝟙} act = one
action-rename-suc {k} {A = A ⨟ B} (seq act) = seq (action-rename-suc {k} act)
action-rename-suc {k} {A = A ⨟ B} (seqε emp act) = seqε (empty-rename-suc {k} emp) (action-rename-suc {k} act)
action-rename-suc {A = A & B} act = amp
action-rename-suc {A = A ⊕ B} act = plus
action-rename-suc {A = A ⅋ B} act = par
action-rename-suc {A = A ⊗ B} act = ten
action-rename-suc {A = get x} act = get
action-rename-suc {A = put x} act = put
action-rename-suc {k} {A = rec A} (rec act) = rec (action-rename-suc {suc k} act)

empty-exts∗-s-just : ∀{k n r} {A : PreType n (suc r)} (x : Fin (suc k + r)) →
                    Empty (exts∗ k (s-just (rec A)) x) → Empty (rec A)
empty-exts∗-s-just {zero} zero emp = emp
empty-exts∗-s-just {suc k} (suc x) emp = empty-exts∗-s-just x (empty-rename-suc {0} emp)

action-exts∗-s-just : ∀{k n r} {A : PreType n (suc r)} (x : Fin (suc k + r)) →
                      Action (exts∗ k (s-just (rec A)) x) → Action (rec A)
action-exts∗-s-just {zero} zero act = act
action-exts∗-s-just {suc k} (suc x) act = action-exts∗-s-just x (action-rename-suc {0} act)

empty-rec-subst : ∀{k n r} {A : PreType n (suc r)} (B : PreType n (suc k + r)) →
                  Empty (rec-subst (exts∗ k (s-just (rec A))) B) → Empty B ⊎ Empty (rec A)
empty-rec-subst (var x) emp = inj₁ var
empty-rec-subst (rav x) emp = inj₁ rav
empty-rec-subst skip emp = inj₁ skip
empty-rec-subst {A = A} (B ⨟ C) (seq eb ec) with empty-rec-subst {A = A} B eb | empty-rec-subst {A = A} C ec
... | inj₁ eb' | inj₁ ec' = inj₁ (seq eb' ec')
... | inj₁ eb' | inj₂ ea = inj₂ ea
... | inj₂ ea | _ = inj₂ ea
empty-rec-subst (inv x) emp = inj₂ (empty-exts∗-s-just x emp)
empty-rec-subst {A = A} (rec B) (rec emp) with empty-rec-subst {A = A} B emp
... | inj₁ x = inj₁ (rec x)
... | inj₂ y = inj₂ y

-- empty-s-just : ∀{k n r} {A : PreType n (suc r)} (x : Fin (suc (k + r))) →
--                Empty (rec A) → ¬ Empty (exts∗ k (s-just (rec A)) x)
-- empty-s-just {zero} zero emp emp' = {!!}
-- empty-s-just {suc k} x emp emp' = {!!}

-- empty-empty : ∀{k n r} {A : PreType n (suc r)} (B : PreType n (suc k + r)) →
--               Empty (rec A) → Empty (rec-subst (exts∗ k (s-just (rec A))) B) → Empty B
-- empty-empty (var x) emp emp' = var
-- empty-empty (rav x) emp emp' = rav
-- empty-empty skip emp emp' = skip
-- empty-empty (B ⨟ C) emp (seq emp' emp'') = seq (empty-empty B emp emp') (empty-empty C emp emp'')
-- empty-empty (inv x) emp emp' = {!!}
-- empty-empty (rec B) emp (rec emp') = rec (empty-empty B emp emp')

action-rec-subst : ∀{k n r} {A : PreType n (suc r)} (B : PreType n (suc k + r)) →
                   Action (rec-subst (exts∗ k (s-just (rec A))) B) →
                   Action B ⊎ Action (rec A) ⊎ Empty (rec A)
action-rec-subst (var _) x = inj₁ var
action-rec-subst (rav _) x = inj₁ rav
action-rec-subst ⊤ top = inj₁ top
action-rec-subst 𝟘 zero = inj₁ zero
action-rec-subst ⊥ bot = inj₁ bot
action-rec-subst 𝟙 one = inj₁ one
action-rec-subst {A = A} (B ⨟ C) (seq act) with action-rec-subst {A = A} B act
... | inj₁ x = inj₁ (seq x)
... | inj₂ y = inj₂ y
action-rec-subst {k} {A = A} (B ⨟ C) (seqε sk act) with empty-rec-subst {A = A} B sk | action-rec-subst {A = A} C act
... | inj₁ x | inj₁ y = inj₁ (seqε x y)
... | inj₁ x | inj₂ y = inj₂ y
... | inj₂ x | inj₁ y = {!!} -- inj₂ (inj₂ x)
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

action-rec-subst' : ∀{k n r} {A : PreType n (suc r)} (B : PreType n (suc k + r)) →
                    ¬ Empty (rec A) → Action (rec-subst (exts∗ k (s-just (rec A))) B) →
                    Action B ⊎ Action (rec A)
action-rec-subst' (var x) nemp act = inj₁ var
action-rec-subst' (rav x) nemp act = inj₁ rav
action-rec-subst' ⊤ nemp act = inj₁ top
action-rec-subst' 𝟘 nemp act = inj₁ zero
action-rec-subst' ⊥ nemp act = inj₁ bot
action-rec-subst' 𝟙 nemp act = inj₁ one
action-rec-subst' {A = A} (B ⨟ C) nemp (seq act) with action-rec-subst' {A = A} B nemp act
... | inj₁ x = inj₁ (seq x)
... | inj₂ y = inj₂ y
action-rec-subst' {A = A} (B ⨟ C) nemp (seqε emp act) with empty-rec-subst {A = A} B emp | action-rec-subst' {A = A} C nemp act
... | inj₁ x | inj₁ y = inj₁ (seqε x y)
... | inj₁ x | inj₂ y = inj₂ y
... | inj₂ x | _ = contradiction x nemp
action-rec-subst' (B & C) nemp act = inj₁ amp
action-rec-subst' (B ⊕ C) nemp act = inj₁ plus
action-rec-subst' (B ⅋ C) nemp act = inj₁ par
action-rec-subst' (B ⊗ C) nemp act = inj₁ ten
action-rec-subst' (get x) nemp act = inj₁ get
action-rec-subst' (put x) nemp act = inj₁ put
action-rec-subst' (inv x) nemp act = inj₂ (action-exts∗-s-just x act)
action-rec-subst' {A = A} (rec B) nemp (rec act) with action-rec-subst' {A = A} B nemp act
... | inj₁ x = inj₁ (rec x)
... | inj₂ y = inj₂ y

empty-unfold : ∀{n r} {A : PreType n (suc r)} → Empty (unfold A) → Empty (rec A)
empty-unfold {A = A} emp with empty-rec-subst {A = A} A emp
... | inj₁ ea = rec ea
... | inj₂ ea = ea

action-unfold : ∀{n r} {A : PreType n (suc r)} → Action (unfold A) → Action (rec A)
action-unfold {A = A} act with action-rec-subst {A = A} A act
... | inj₁ x = rec x
... | inj₂ (inj₁ x) = x
... | inj₂ (inj₂ (rec x)) = {!_!} -- contradiction act (empty-not-action (empty-after-rec-subst x))

action-unfold' : ∀{n r} {A : PreType n (suc r)} → ¬ Empty (rec A) → Action (unfold A) → Action (rec A)
action-unfold' {A = A} nemp act with action-rec-subst' {A = A} A nemp act
... | inj₁ x = rec x
... | inj₂ x = x

lemma : ∀{n r ℓ} {A B : PreType n r} → ℓ ≢ ε → A ⊨ ℓ ⇒ B → ¬ Empty A
lemma ne skip skip = ne refl
lemma ne (seq tr x) (seq emp emp₁) = {!!}
lemma ne (seqε tr tr₁) (seq emp emp₁) = {!!}
lemma ne (seq⊗ tr) (seq emp emp₁) = {!!}
lemma ne (seq⅋ tr) (seq emp emp₁) = {!!}
lemma ne (rec tr) (rec emp) = {!!}

-- empty-complete : ∀{n r} {A : PreType n r} → A ⊨ ε ⇒ skip → Empty A
-- empty-complete skip = skip
-- empty-complete (seqε x y) = seq (empty-complete x) (empty-complete y)
-- empty-complete (rec x) = empty-unfold (empty-complete x)

-- action-complete : ∀{n r ℓ} {A B : PreType n r} → ℓ ≢ ε → A ⊨ ℓ ⇒ B → Action A
-- action-complete ne skip = contradiction refl ne
-- action-complete ne ⊥ = bot
-- action-complete ne 𝟙 = one
-- action-complete ne ⊤ = top
-- action-complete ne 𝟘 = zero
-- action-complete ne &L = amp
-- action-complete ne &R = amp
-- action-complete ne ⊕L = plus
-- action-complete ne ⊕R = plus
-- action-complete ne ⅋L = par
-- action-complete ne ⅋R = par
-- action-complete ne ⊗L = ten
-- action-complete ne ⊗R = ten
-- action-complete ne (seq x _) = seq (action-complete ne x)
-- action-complete ne (seqε x y) = seqε (empty-complete x) (action-complete ne y)
-- action-complete ne (seq⊗ x) = seq (action-complete ne x)
-- action-complete ne (seq⅋ x) = seq (action-complete ne x)
-- action-complete ne put = put
-- action-complete ne get = get
-- action-complete ne (rec x) = action-unfold (action-complete ne x)

empty-complete-subst : ∀{m n r} (A : PreType m r) {σ : Substitution m n} →
                       subst σ A ⊨ ε ⇒ skip → Empty A
empty-complete-subst (var x) tr = var
empty-complete-subst (rav x) tr = rav
empty-complete-subst skip tr = skip
empty-complete-subst (A ⨟ B) (seqε tr tr') = seq (empty-complete-subst A tr) (empty-complete-subst B tr')
empty-complete-subst (rec A) {σ} (rec tr)
  rewrite unfold-subst σ A
  with empty-complete-subst (unfold A) tr
... | emp = empty-unfold emp

action-complete-subst : ∀{m n r ℓ} (A : PreType m r) {B : PreType n r} {σ : Substitution m n} →
                        ℓ ≢ ε → subst σ A ⊨ ℓ ⇒ B → Action A
action-complete-subst (var x) ne tr = var
action-complete-subst (rav x) ne tr = rav
action-complete-subst skip ne skip = contradiction refl ne
action-complete-subst ⊤ ne tr = top
action-complete-subst 𝟘 ne tr = zero
action-complete-subst ⊥ ne tr = bot
action-complete-subst 𝟙 ne tr = one
action-complete-subst (A ⨟ B) ne (seq tr ns) = seq (action-complete-subst A ne tr)
action-complete-subst (A ⨟ B) ne (seqε sk tr) = seqε (empty-complete-subst A sk) (action-complete-subst B {!!} tr)
action-complete-subst (A ⨟ B) ne (seq⊗ tr) = seq (action-complete-subst A ne tr)
action-complete-subst (A ⨟ B) ne (seq⅋ tr) = seq (action-complete-subst A ne tr)
action-complete-subst (A & B) ne tr = amp
action-complete-subst (A ⊕ B) ne tr = plus
action-complete-subst (A ⅋ B) ne tr = par
action-complete-subst (A ⊗ B) ne tr = ten
action-complete-subst (get x) ne tr = get
action-complete-subst (put x) ne tr = put
action-complete-subst (rec A) {σ = σ} ne (rec tr)
  rewrite unfold-subst σ A with action-complete-subst (unfold A) ne tr
... | act = action-unfold act

visible-complete-subst : ∀{m n r ℓ} (A : PreType m r) {B : PreType n r} {σ : Substitution m n} →
                         subst σ A ⊨ ℓ ⇒ B → (Empty A × Action A) ⊎ (ℓ ≡ ε × Empty A × ¬ Action A) ⊎ (ℓ ≢ ε × ¬ Empty A × Action A)
visible-complete-subst (var x) tr = inj₁ (var , var)
visible-complete-subst (rav x) tr = inj₁ (rav , rav)
visible-complete-subst skip skip = inj₂ (inj₁ (refl , skip , λ ()))
visible-complete-subst ⊤ ⊤ = inj₂ (inj₂ ((λ ()) , (λ ()) , top))
visible-complete-subst 𝟘 𝟘 = inj₂ (inj₂ ((λ ()) , (λ ()) , zero))
visible-complete-subst ⊥ tr = {!!}
visible-complete-subst 𝟙 tr = {!!}
visible-complete-subst (A ⨟ B) (seq tr ns) with visible-complete-subst A tr
... | inj₂ (inj₁ (refl , x)) = contradiction ε ns
... | inj₂ (inj₂ (ne , nemp , act)) = inj₂ (inj₂ (ne , (λ { (seq emp _) → nemp emp}) , seq act))
... | inj₁ (emp , act) with Empty-dec B
... | inj₁ x = inj₁ (seq emp x , seq act)
... | inj₂ x = inj₂ (inj₂ ({!!} , (λ { (seq y z) → x z}) , seq act))
visible-complete-subst (A ⨟ B) (seqε sk tr) with visible-complete-subst A sk | visible-complete-subst B tr
... | inj₁ (aemp , aact) | inj₁ (bemp , bact) = inj₁ {!!}
... | inj₁ x | inj₂ y = {!!}
... | inj₂ x | y = {!!}
visible-complete-subst (A ⨟ B) (seq⊗ tr) = {!!}
visible-complete-subst (A ⨟ B) (seq⅋ tr) = {!!}
visible-complete-subst (A & B) tr = {!!}
visible-complete-subst (A ⊕ B) tr = {!!}
visible-complete-subst (A ⅋ B) tr = {!!}
visible-complete-subst (A ⊗ B) tr = {!!}
visible-complete-subst (get x) tr = {!!}
visible-complete-subst (put x) tr = {!!}
visible-complete-subst (rec A) tr = {!!}

-- visible-complete : ∀{n r ℓ} {A B : PreType n r} → A ⊨ ℓ ⇒ B → Visible A
-- visible-complete {ℓ = ℓ} tr with special-decidable ℓ
-- ... | inj₂ ns = inj₂ (action-complete (λ { refl → ns ε }) tr)
-- ... | inj₁ ε = inj₁ (empty-complete (Eq.subst (_ ⊨ _ ⇒_) (afterεskip tr) tr))
-- ... | inj₁ ⊗L = inj₂ (action-complete (λ ()) tr)
-- ... | inj₁ ⅋L = inj₂ (action-complete (λ ()) tr)
