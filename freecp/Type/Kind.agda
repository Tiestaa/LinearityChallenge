{-# OPTIONS --rewriting --guardedness #-}
module Type.Kind where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂)

open import Type
open import Type.Renaming
open import Type.Unfolding
open import Type.Substitution
open import Type.Transitions

data Kind (n : ℕ) : Set where
  ε • ∗ : Kind n
  var   : Fin n → Kind n → Kind n

_>>_ : ∀{n} → Kind n → Kind n → Kind n
ε >> k' = k'
• >> k' = •
∗ >> k' = ∗
var x k >> k' = var x (k >> k')

>>-assoc : ∀{n} (k k' k'' : Kind n) → (k >> k') >> k'' ≡ k >> (k' >> k'')
>>-assoc ε k' k'' = refl
>>-assoc • k' k'' = refl
>>-assoc ∗ k' k'' = refl
>>-assoc (var x k) k' k'' = cong (var x) (>>-assoc k k' k'')

>>-idempotent : (k : Kind 0) → k >> k ≡ k
>>-idempotent ε = refl
>>-idempotent • = refl
>>-idempotent ∗ = refl

>>ε-l : ∀{n} {k k' : Kind n} → k >> k' ≡ ε → k ≡ ε
>>ε-l {_} {ε} {ε} refl = refl

>>ε-r : ∀{n} {k k' : Kind n} → k >> k' ≡ ε → k' ≡ ε
>>ε-r {_} {ε} {ε} refl = refl

>>-weird : (k k' k'' : Kind 0) → k' >> k ≡ k' >> k'' ⊎ k' >> k ≡ k
>>-weird k ε k'' = inj₂ refl
>>-weird k • k'' = inj₁ refl
>>-weird k ∗ k'' = inj₁ refl

>>-weirder : (k k' k'' : Kind 0) → (k ≡ ε → k' >> k'' ≡ ε) → k >> k'' ≡ k' >> k'' ⊎ k >> k'' ≡ k
>>-weirder ε k' k'' hyp = inj₂ (>>ε-r (hyp refl))
>>-weirder • k' k'' hyp = inj₂ refl
>>-weirder ∗ k' k'' hyp = inj₂ refl

>>• : ∀{n} {k k' : Kind n} → k >> k' ≡ • → k ≡ • ⊎ (k ≡ ε × k' ≡ •)
>>• {_} {ε} eq = inj₂ (refl , eq)
>>• {_} {•} eq = inj₁ eq

>>∗ : ∀{n} {k k' : Kind n} → k >> k' ≢ ∗ → k ≢ ∗
>>∗ {_} {ε} {_} ne = λ ()
>>∗ {_} {•} {_} ne = λ ()
>>∗ {_} {∗} {_} ne = ne
>>∗ {_} {var x k} {_} ne = λ ()

>>∗' : ∀{n} {k k' : Kind n} → k >> k' ≡ ∗ → k ≡ ∗ ⊎ (k ≡ ε × k' ≡ ∗)
>>∗' {_} {ε} {k'} eq = inj₂ (refl , eq)
>>∗' {_} {∗} {k'} eq = inj₁ eq

ε-unit-r : ∀{n} (k : Kind n) → k >> ε ≡ k
ε-unit-r ε = refl
ε-unit-r • = refl
ε-unit-r ∗ = refl
ε-unit-r (var x k) = cong (var x) (ε-unit-r k)

kind : ∀{n r} → PreType n r → Kind n
kind (var x) = var x ε
kind (rav x) = var x ε
kind skip = ε
kind ⊤ = •
kind 𝟘 = •
kind ⊥ = •
kind 𝟙 = •
kind (A ⨟ B) = kind A >> kind B
kind (A & B) = •
kind (A ⊕ B) = •
kind (A ⅋ B) = •
kind (A ⊗ B) = •
kind (get x) = •
kind (put x) = •
kind (inv x) = ∗
kind (rec A) = kind A

kind-dual : ∀{n r} (A : PreType n r) → kind (dual A) ≡ kind A
kind-dual (var x) = refl
kind-dual (rav x) = refl
kind-dual skip = refl
kind-dual ⊤ = refl
kind-dual 𝟘 = refl
kind-dual ⊥ = refl
kind-dual 𝟙 = refl
kind-dual (A ⨟ B) = cong₂ _>>_ (kind-dual A) (kind-dual B)
kind-dual (A & B) = refl
kind-dual (A ⊕ B) = refl
kind-dual (A ⅋ B) = refl
kind-dual (A ⊗ B) = refl
kind-dual (get x) = refl
kind-dual (put x) = refl
kind-dual (inv x) = refl
kind-dual (rec A) = kind-dual A

KindSubstitution : ℕ → ℕ → Set
KindSubstitution m n = Fin m → Kind n

k-subst : ∀{m n} (κ : KindSubstitution m n) → Kind m → Kind n
k-subst κ ε = ε
k-subst κ • = •
k-subst κ ∗ = ∗
k-subst κ (var x k) = κ x >> k-subst κ k

action-k-subst : ∀{n} → KindSubstitution n 0
action-k-subst _ = •

valid-k-subst : ∀{n} (k : Kind n) → k ≢ ∗ → k-subst action-k-subst k ≡ ε ⊎ k-subst action-k-subst k ≡ •
valid-k-subst ε ne = inj₁ refl
valid-k-subst • ne = inj₂ refl
valid-k-subst ∗ ne = contradiction refl ne
valid-k-subst (var x k) ne = inj₂ refl

k-subst>> : ∀{m n} (κ : KindSubstitution m n) (k k' : Kind m) →
            k-subst κ k >> k-subst κ k' ≡ k-subst κ (k >> k')
k-subst>> κ ε k' = refl
k-subst>> κ • k' = refl
k-subst>> κ ∗ k' = refl
k-subst>> κ (var x k) k' = begin
    (k-subst κ (var x k) >> k-subst κ k') ≡⟨ refl ⟩
    (κ x >> k-subst κ k) >> k-subst κ k' ≡⟨ >>-assoc (κ x) (k-subst κ k) (k-subst κ k') ⟩
    κ x >> (k-subst κ k >> k-subst κ k') ≡⟨ cong (κ x >>_) (k-subst>> κ k k') ⟩
    κ x >> (k-subst κ (k >> k')) ≡⟨ refl ⟩
    k-subst κ (var x k >> k') ∎
  where open Eq.≡-Reasoning

Kinding : ∀{m n} → Substitution m n → KindSubstitution m n → Set
Kinding σ κ = ∀ x → ∀{r} → kind (σ .at {r} x) ≡ κ x

kinding-action-subst : ∀{n} → Kinding {n} {0} action-subst action-k-subst
kinding-action-subst _ = refl

kind-subst : ∀{m n r} (A : PreType m r) {σ : Substitution m n} {κ : KindSubstitution m n} →
             Kinding σ κ → kind (subst σ A) ≡ k-subst κ (kind A)
kind-subst (var x) {σ} {κ} kind rewrite ε-unit-r (κ x) = kind x
kind-subst (rav x) {σ} {κ} kind rewrite ε-unit-r (κ x) = Eq.trans (kind-dual (σ .at x)) (kind x)
kind-subst skip kind = refl
kind-subst ⊤ kind = refl
kind-subst 𝟘 kind = refl
kind-subst ⊥ kind = refl
kind-subst 𝟙 kind = refl
kind-subst (A ⨟ B) {σ} {κ} kinding = begin
    kind (subst σ (A ⨟ B)) ≡⟨ refl ⟩
    kind (subst σ A ⨟ subst σ B) ≡⟨ refl ⟩
    kind (subst σ A) >> kind (subst σ B) ≡⟨ cong₂ _>>_ (kind-subst A kinding) (kind-subst B kinding) ⟩
    k-subst κ (kind A) >> k-subst κ (kind B) ≡⟨ k-subst>> κ (kind A) (kind B) ⟩
    k-subst κ (kind (A ⨟ B)) ∎
  where open Eq.≡-Reasoning
kind-subst (A & B) kind = refl
kind-subst (A ⊕ B) kind = refl
kind-subst (A ⅋ B) kind = refl
kind-subst (A ⊗ B) kind = refl
kind-subst (get x) kind = refl
kind-subst (put x) kind = refl
kind-subst (inv x) kind = refl
kind-subst (rec A) kind = kind-subst A kind

label-kind : ∀{n} → Label → Kind n
label-kind ε = ε
label-kind ⊥ = •
label-kind 𝟙 = •
label-kind ⊤ = •
label-kind 𝟘 = •
label-kind &L = •
label-kind &R = •
label-kind ⊕L = •
label-kind ⊕R = •
label-kind ⅋L = •
label-kind ⅋R = •
label-kind ⊗L = •
label-kind ⊗R = •
label-kind (put x) = •
label-kind (get x) = •

-- SOUNDNESS

ε-sound : ∀{n r} (A : PreType n r) → kind A ≡ ε → A ⊨ ε ⇒ skip
ε-sound skip eq = skip
ε-sound (A ⨟ B) eq = seqε (ε-sound A (>>ε-l eq)) (ε-sound B (>>ε-r eq))
ε-sound (rec A) eq = rec (transition-unfold (ε-sound A eq))

•-sound : ∀{n r} (A : PreType n r) → kind A ≡ • → ∃[ ℓ ] ∃[ B ] label-kind ℓ ≡ kind A × A ⊨ ℓ ⇒ B
•-sound ⊤ eq = ⊤ , ⊤ , eq , ⊤
•-sound 𝟘 eq = 𝟘 , 𝟘 , eq , 𝟘
•-sound ⊥ eq = ⊥ , ⊥ , eq , ⊥
•-sound 𝟙 eq = 𝟙 , 𝟙 , eq , 𝟙
•-sound (A ⨟ B) eq with >>• eq
•-sound (A ⨟ B) eq | inj₁ eq' with •-sound A eq'
... | ℓ , _ , eq'' , tr with special-decidable ℓ
... | inj₂ ns = _ , _ , Eq.trans eq'' (Eq.trans eq' (Eq.sym eq)) , seq tr ns
•-sound (A ⨟ B) eq | inj₁ eq' | ε , _ , eq'' , tr | inj₁ sp = contradiction (Eq.trans eq'' eq') λ ()
•-sound (A ⨟ B) eq | inj₁ eq' | ⅋L , _ , eq'' , tr | inj₁ sp = _ , _ , Eq.sym eq , seq⅋ tr
•-sound (A ⨟ B) eq | inj₁ eq' | ⊗L , _ , eq'' , tr | inj₁ sp = _ , _ , Eq.sym eq , seq⊗ tr
•-sound (A ⨟ B) eq | inj₂ (eq' , eq'') with •-sound B eq''
... | _ , _ , eq''' , tr = _ , _ , Eq.trans eq''' (Eq.trans eq'' (Eq.sym eq)) , seqε (ε-sound A eq') tr
•-sound (A & B) eq = &L , A , eq , &L
•-sound (A ⊕ B) eq = ⊕L , A , eq , ⊕L
•-sound (A ⅋ B) eq = ⅋L , A , eq , ⅋L
•-sound (A ⊗ B) eq = ⊗L , A , eq , ⊗L
•-sound (get x) eq = get x , skip , eq , get
•-sound (put x) eq = put x , skip , eq , put
•-sound (rec A) eq with •-sound A eq
... | _ , _ , eq' , tr = _ , _ , eq' , rec (transition-unfold tr)

kind-sound : ∀{n r} (A : PreType n r) → kind A ≢ ∗ → Σ[ σ ∈ Substitution n 0 ] ∃[ ℓ ] ∃[ B ] subst σ A ⊨ ℓ ⇒ B
kind-sound A ne with valid-k-subst (kind A) ne
... | inj₁ eq = action-subst , ε , _ , ε-sound (subst action-subst A) (Eq.trans (kind-subst A kinding-action-subst) eq)
... | inj₂ eq with •-sound (subst action-subst A) (Eq.trans (kind-subst A kinding-action-subst) eq)
... | ℓ , B , eq' , tr = action-subst , ℓ , B , tr

-- COMPLETENESS

kind-rename-suc : ∀{k n r} (A : PreType n (k + r)) → kind (rename (ext∗ {r} k suc) A) ≡ kind A
kind-rename-suc (var x) = refl
kind-rename-suc (rav x) = refl
kind-rename-suc skip = refl
kind-rename-suc ⊤ = refl
kind-rename-suc 𝟘 = refl
kind-rename-suc ⊥ = refl
kind-rename-suc 𝟙 = refl
kind-rename-suc {k} {r = r} (A ⨟ B) = cong₂ _>>_ (kind-rename-suc {k} {r = r} A) (kind-rename-suc {k} {r = r} B)
kind-rename-suc (A & B) = refl
kind-rename-suc (A ⊕ B) = refl
kind-rename-suc (A ⅋ B) = refl
kind-rename-suc (A ⊗ B) = refl
kind-rename-suc (get x) = refl
kind-rename-suc (put x) = refl
kind-rename-suc (inv x) = refl
kind-rename-suc {k} {n} {r} (rec A) = kind-rename-suc {suc k} {n} {r} A

kind-exts∗-s-just : ∀{k n r} {A : PreType n (suc r)} (x : Fin (suc k + r)) →
                    kind (exts∗ k (s-just (rec A)) x) ≡ ∗ ⊎
                    kind (exts∗ k (s-just (rec A)) x) ≡ kind A
kind-exts∗-s-just {zero} zero = inj₂ refl
kind-exts∗-s-just {zero} (suc x) = inj₁ refl
kind-exts∗-s-just {suc k} zero = inj₁ refl
kind-exts∗-s-just {suc k} {A = A} (suc x) rewrite kind-rename-suc {0} (exts∗ k (s-just (rec A)) x) =
  kind-exts∗-s-just {A = A} x

kind-rec-subst : ∀{k r} {A : PreType 0 (suc r)} (B : PreType 0 (suc k + r)) →
                 (kind A ≡ ε → kind B ≡ ε) →
                 kind (rec-subst (exts∗ k (s-just (rec A))) B) ≡ kind B ⊎
                 kind (rec-subst (exts∗ k (s-just (rec A))) B) ≡ kind A
kind-rec-subst (var x) hyp = inj₁ refl
kind-rec-subst (rav x) hyp = inj₁ refl
kind-rec-subst skip hyp = inj₁ refl
kind-rec-subst ⊤ hyp = inj₁ refl
kind-rec-subst 𝟘 hyp = inj₁ refl
kind-rec-subst ⊥ hyp = inj₁ refl
kind-rec-subst 𝟙 hyp = inj₁ refl
kind-rec-subst {A = A} (B ⨟ C) hyp
  with kind-rec-subst {A = A} B (λ eq → >>ε-l (hyp eq)) |
       kind-rec-subst {A = A} C (λ eq → >>ε-r (hyp eq))
... | inj₁ x | inj₁ y = inj₁ (cong₂ _>>_ x y)
... | inj₁ x | inj₂ y rewrite x | y = >>-weird (kind A) (kind B) (kind C)
... | inj₂ x | inj₁ y rewrite x | y = >>-weirder (kind A) (kind B) (kind C) hyp
... | inj₂ x | inj₂ y rewrite x | y = inj₂ (>>-idempotent (kind A))
kind-rec-subst (B & C) hyp = inj₁ refl
kind-rec-subst (B ⊕ C) hyp = inj₁ refl
kind-rec-subst (B ⅋ C) hyp = inj₁ refl
kind-rec-subst (B ⊗ C) hyp = inj₁ refl
kind-rec-subst (get x) hyp = inj₁ refl
kind-rec-subst (put x) hyp = inj₁ refl
kind-rec-subst {A = A} (inv x) hyp = kind-exts∗-s-just {A = A} x
kind-rec-subst {A = A} (rec B) hyp = kind-rec-subst {A = A} B hyp

kind-unfold : ∀{r} (A : PreType 0 (suc r)) → kind (unfold A) ≡ kind A
kind-unfold A with kind-rec-subst {A = A} A (λ eq → eq)
... | inj₁ x = x
... | inj₂ x = x

ε-complete : ∀{r} {A : PreType 0 r} → A ⊨ ε ⇒ skip → kind A ≡ ε
ε-complete skip = refl
ε-complete (seqε tr tr') rewrite ε-complete tr | ε-complete tr' = refl
ε-complete {A = rec A} (rec tr) = Eq.trans (Eq.sym (kind-unfold A)) (ε-complete tr)

•-complete : ∀{r ℓ} {A B : PreType 0 r} → ℓ ≢ ε → A ⊨ ℓ ⇒ B → kind A ≡ •
•-complete ne skip = contradiction refl ne
•-complete ne ⊥ = refl
•-complete ne 𝟙 = refl
•-complete ne ⊤ = refl
•-complete ne 𝟘 = refl
•-complete ne &L = refl
•-complete ne &R = refl
•-complete ne ⊕L = refl
•-complete ne ⊕R = refl
•-complete ne ⅋L = refl
•-complete ne ⅋R = refl
•-complete ne ⊗L = refl
•-complete ne ⊗R = refl
•-complete ne (seq tr ns) rewrite •-complete ne tr = refl
•-complete ne (seqε sk tr) rewrite ε-complete sk = •-complete ne tr
•-complete ne (seq⊗ tr) rewrite •-complete ne tr = refl
•-complete ne (seq⅋ tr) rewrite •-complete ne tr = refl
•-complete ne put = refl
•-complete ne get = refl
•-complete {A = rec A} ne (rec tr) = Eq.trans (Eq.sym (kind-unfold A)) (•-complete ne tr)

ε-preserved : ∀{n r} (A : PreType n r) (σ : Substitution n 0) → kind A ≡ ε → kind (subst σ A) ≡ ε
ε-preserved skip σ eq = refl
ε-preserved (A ⨟ B) σ eq rewrite ε-preserved A σ (>>ε-l eq) | ε-preserved B σ (>>ε-r eq) = refl
ε-preserved (rec A) σ eq = ε-preserved A σ eq

∗-preserved : ∀{n r} (A : PreType n r) (σ : Substitution n 0) → kind A ≡ ∗ → kind (subst σ A) ≡ ∗
∗-preserved (A ⨟ B) σ eq with >>∗' {_} {kind A} {kind B} eq
... | inj₁ eq' rewrite ∗-preserved A σ eq' = refl
... | inj₂ (eq' , eq'') rewrite ε-preserved A σ eq' = ∗-preserved B σ eq''
∗-preserved (inv x) σ eq = refl
∗-preserved (rec A) σ eq = ∗-preserved A σ eq

kind-complete : ∀{n r ℓ} (A : PreType n r) {B : PreType 0 r} (σ : Substitution n 0) →
                subst σ A ⊨ ℓ ⇒ B → kind A ≢ ∗
kind-complete {ℓ = ℓ} A σ tr ast with special-decidable ℓ
kind-complete {ℓ = ℓ} A σ tr ast | inj₁ ε with afterεskip tr
... | refl with Eq.trans (Eq.sym (ε-complete tr)) (∗-preserved A σ ast)
... | ()
kind-complete {ℓ = ℓ} A σ tr ast | inj₁ ⊗L with Eq.trans (Eq.sym (•-complete (λ ()) tr)) (∗-preserved A σ ast)
... | ()
kind-complete {ℓ = ℓ} A σ tr ast | inj₁ ⅋L  with Eq.trans (Eq.sym (•-complete (λ ()) tr)) (∗-preserved A σ ast)
... | ()
kind-complete {ℓ = ℓ} A σ tr ast | inj₂ ns with Eq.trans (Eq.sym (•-complete (not-special-not-ε ns) tr)) (∗-preserved A σ ast)
... | ()
