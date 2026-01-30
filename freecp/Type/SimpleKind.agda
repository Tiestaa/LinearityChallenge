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
open import Type.Substitutions

depth : ∀{n r} → PreType n r → ℕ
depth (var x) = 0
depth (rav x) = 0
depth skip = 0
depth ⊤ = 0
depth 𝟘 = 0
depth ⊥ = 0
depth 𝟙 = 0
depth (A ⨟ B) = depth A ⊔ depth B
depth (A & B) = depth A ⊔ depth B
depth (A ⊕ B) = depth A ⊔ depth B
depth (A ⅋ B) = depth A ⊔ depth B
depth (A ⊗ B) = depth A ⊔ depth B
depth (get x) = 0
depth (put x) = 0
depth (inv x) = 0
depth (rec A) = suc (depth A)

data _⊢_⊨_⇒_ {n r} : ℕ → PreType n r → Label → PreType n r → Set where
  skip : ∀{f} → f ⊢ skip ⊨ ε ⇒ skip
  ⊥    : ∀{f} → f ⊢ ⊥ ⊨ ⊥ ⇒ ⊥
  𝟙    : ∀{f} → f ⊢ 𝟙 ⊨ 𝟙 ⇒ 𝟙
  ⊤    : ∀{f} → f ⊢ ⊤ ⊨ ⊤ ⇒ ⊤
  𝟘    : ∀{f} → f ⊢ 𝟘 ⊨ 𝟘 ⇒ 𝟘
  &L   : ∀{f A B} → f ⊢ (A & B) ⊨ &L ⇒ A
  &R   : ∀{f A B} → f ⊢ (A & B) ⊨ &R ⇒ B
  ⊕L   : ∀{f A B} → f ⊢ (A ⊕ B) ⊨ ⊕L ⇒ A
  ⊕R   : ∀{f A B} → f ⊢ (A ⊕ B) ⊨ ⊕R ⇒ B
  ⅋L   : ∀{f A B} → f ⊢ (A ⅋ B) ⊨ ⅋L ⇒ A
  ⅋R   : ∀{f A B} → f ⊢ (A ⅋ B) ⊨ ⅋R ⇒ B
  ⊗L   : ∀{f A B} → f ⊢ (A ⊗ B) ⊨ ⊗L ⇒ A
  ⊗R   : ∀{f A B} → f ⊢ (A ⊗ B) ⊨ ⊗R ⇒ B
  seq  : ∀{f A B C ℓ} → f ⊢ A ⊨ ℓ ⇒ B → ¬ Special ℓ → f ⊢ (A ⨟ C) ⊨ ℓ ⇒ (B ⨟ C)
  seqε : ∀{f A B C ℓ} → f ⊢ A ⊨ ε ⇒ skip → f ⊢ B ⊨ ℓ ⇒ C → f ⊢ (A ⨟ B) ⊨ ℓ ⇒ C
  seq⊗ : ∀{f A B C} → f ⊢ A ⊨ ⊗L ⇒ C → f ⊢ (A ⨟ B) ⊨ ⊗L ⇒ C
  seq⅋ : ∀{f A B C} → f ⊢ A ⊨ ⅋L ⇒ C → f ⊢ (A ⨟ B) ⊨ ⅋L ⇒ C
  put  : ∀{f μ} → f ⊢ put μ ⊨ put μ ⇒ skip
  get  : ∀{f μ} → f ⊢ get μ ⊨ get μ ⇒ skip
  rec  : ∀{f A B ℓ} → f ⊢ unfold A ⊨ ℓ ⇒ B → suc f ⊢ rec A ⊨ ℓ ⇒ B

more-fuel : ∀{n r ℓ f g} {A B : PreType n r} → f ≤ g → f ⊢ A ⊨ ℓ ⇒ B → g ⊢ A ⊨ ℓ ⇒ B
more-fuel le skip = skip
more-fuel le ⊥ = ⊥
more-fuel le 𝟙 = 𝟙
more-fuel le ⊤ = ⊤
more-fuel le 𝟘 = 𝟘
more-fuel le &L = &L
more-fuel le &R = &R
more-fuel le ⊕L = ⊕L
more-fuel le ⊕R = ⊕R
more-fuel le ⅋L = ⅋L
more-fuel le ⅋R = ⅋R
more-fuel le ⊗L = ⊗L
more-fuel le ⊗R = ⊗R
more-fuel le (seq x y) = seq (more-fuel le x) y
more-fuel le (seqε x y) = seqε (more-fuel le x) (more-fuel le y)
more-fuel le (seq⊗ x) = seq⊗ (more-fuel le x)
more-fuel le (seq⅋ x) = seq⅋ (more-fuel le x)
more-fuel le put = put
more-fuel le get = get
more-fuel (s≤s le) (rec x) = rec (more-fuel le x)

fueled-transition : ∀{n r ℓ} {A B : PreType n r} → A ⊨ ℓ ⇒ B → ∃[ f ] f ⊢ A ⊨ ℓ ⇒ B
fueled-transition skip = 0 , skip
fueled-transition ⊥ = 0 , ⊥
fueled-transition 𝟙 = 0 , 𝟙
fueled-transition ⊤ = 0 , ⊤
fueled-transition 𝟘 = 0 , 𝟘
fueled-transition &L = 0 , &L
fueled-transition &R = 0 , &R
fueled-transition ⊕L = 0 , ⊕L
fueled-transition ⊕R = 0 , ⊕R
fueled-transition ⅋L = 0 , ⅋L
fueled-transition ⅋R = 0 , ⅋R
fueled-transition ⊗L = 0 , ⊗L
fueled-transition ⊗R = 0 , ⊗R
fueled-transition (seq x ns) with fueled-transition x
... | _ , x' = _ , seq x' ns
fueled-transition (seqε x y) with fueled-transition x | fueled-transition y
... | f , x' | g , y' = _ , seqε (more-fuel (m≤m⊔n f g) x') (more-fuel (m≤n⊔m f g) y')
fueled-transition (seq⊗ x) with fueled-transition x
... | _ , x' = _ , seq⊗ x'
fueled-transition (seq⅋ x) with fueled-transition x
... | _ , x' = _ , seq⅋ x'
fueled-transition put = 0 , put
fueled-transition get = 0 , get
fueled-transition (rec x) with fueled-transition x
... | _ , x' = _ , rec x'

transition-fueled : ∀{f n r ℓ} {A B : PreType n r} → f ⊢ A ⊨ ℓ ⇒ B → A ⊨ ℓ ⇒ B
transition-fueled skip = skip
transition-fueled ⊥ = ⊥
transition-fueled 𝟙 = 𝟙
transition-fueled ⊤ = ⊤
transition-fueled 𝟘 = 𝟘
transition-fueled &L = &L
transition-fueled &R = &R
transition-fueled ⊕L = ⊕L
transition-fueled ⊕R = ⊕R
transition-fueled ⅋L = ⅋L
transition-fueled ⅋R = ⅋R
transition-fueled ⊗L = ⊗L
transition-fueled ⊗R = ⊗R
transition-fueled (seq x y) = seq (transition-fueled x) y
transition-fueled (seqε x y) = seqε (transition-fueled x) (transition-fueled y)
transition-fueled (seq⊗ x) = seq⊗ (transition-fueled x)
transition-fueled (seq⅋ x) = seq⅋ (transition-fueled x)
transition-fueled put = put
transition-fueled get = get
transition-fueled (rec x) = rec (transition-fueled x)

data Skip {n r} : PreType n r → Set where
  skip : Skip skip
  var  : ∀{x} → Skip (var x)
  rav  : ∀{x} → Skip (rav x)
  seq  : ∀{A B} → Skip A → Skip B → Skip (A ⨟ B)
  rec  : ∀{A} → Skip (unfold A) → Skip (rec A)

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
  rec  : ∀{A} → Action (unfold A) → Action (rec A)

Converge : ∀{n r} (A : PreType n r) → Set
Converge A = Skip A ⊎ Action A

mutual
  record ∞Diverge {n r} (A : PreType n r) : Set where
    coinductive
    field
      unbox : Diverge A

  data Diverge {n r} : PreType n r → Set where
    inv  : ∀{x} → Diverge (inv x)
    seq  : ∀{A B} → ∞Diverge A → Diverge (A ⨟ B)
    seqε : ∀{A B} → Skip A → ∞Diverge B → Diverge (A ⨟ B)
    rec  : ∀{A} → ∞Diverge (unfold A) → Diverge (rec A)

open ∞Diverge

-- skip-action : ∀{n r} {A : PreType n r} → Skip A → ¬ Action A
-- skip-action = {!!}

-- skip-diverge : ∀{n r} {A : PreType n r} → Skip A → ¬ Diverge A
-- skip-diverge (seq sk _) (seq div) = skip-diverge sk (div .unbox)
-- skip-diverge (seq _ sk) (seqε _ div) = skip-diverge sk (div .unbox)
-- skip-diverge (rec sk) (rec div) = skip-diverge sk (div .unbox )

-- converge-diverge : ∀{n r} {A : PreType n r} → Converge A → ¬ Diverge A
-- converge-diverge (inj₁ (seq sk _)) (seq div) = converge-diverge (inj₁ sk) (div .unbox)
-- converge-diverge (inj₂ (seq y)) (seq x) = converge-diverge (inj₂ y) (x .unbox)
-- converge-diverge (inj₂ (seqε x _)) (seq y) = converge-diverge (inj₁ x) (y .unbox)
-- converge-diverge (inj₁ (seq _ x)) (seqε _ y) = converge-diverge (inj₁ x) (y .unbox)
-- converge-diverge (inj₂ (seq x)) (seqε y _) = contradiction x (skip-action y)
-- converge-diverge (inj₂ (seqε _ x)) (seqε _ y) = converge-diverge (inj₂ x) (y .unbox)
-- converge-diverge (inj₁ (rec x)) (rec y) = converge-diverge (inj₁ x) (y .unbox)
-- converge-diverge (inj₂ (rec x)) (rec y) = converge-diverge (inj₂ x) (y .unbox)

-- not-converge-diverge : ∀{n r} {A : PreType n r} → ¬ Converge A → ∞Diverge A
-- not-converge-diverge {A = var x} nc = contradiction (inj₁ var) nc
-- not-converge-diverge {A = rav x} nc = contradiction (inj₁ rav) nc
-- not-converge-diverge {A = skip} nc = {!!}
-- not-converge-diverge {A = ⊤} nc = {!!}
-- not-converge-diverge {A = 𝟘} nc = {!!}
-- not-converge-diverge {A = ⊥} nc = {!!}
-- not-converge-diverge {A = 𝟙} nc = {!!}
-- not-converge-diverge {A = A ⨟ A₁} nc = {!!}
-- not-converge-diverge {A = A & A₁} nc = {!!}
-- not-converge-diverge {A = A ⊕ A₁} nc = {!!}
-- not-converge-diverge {A = A ⅋ A₁} nc = {!!}
-- not-converge-diverge {A = A ⊗ A₁} nc = {!!}
-- not-converge-diverge {A = get x} nc = {!!}
-- not-converge-diverge {A = put x} nc = {!!}
-- not-converge-diverge {A = inv x} nc = record { unbox = inv }
-- not-converge-diverge {A = rec A} nc .unbox = rec (not-converge-diverge {!!})

-- data IDiverge {n r} : PreType n r → Set where
--   inv  : ∀{x} → IDiverge (inv x)
--   seq  : ∀{A B} → IDiverge A → IDiverge (A ⨟ B)
--   seqε : ∀{A B} → Skip A → IDiverge B → IDiverge (A ⨟ B)
--   rec  : ∀{A} → IDiverge A → IDiverge (rec A)

-- skip-rec-subst : ∀{n r s} {A : PreType n r} {τ : Fin r → PreType n s} →
--                  Skip A → Skip (rec-subst τ A)
-- skip-rec-subst skip = skip
-- skip-rec-subst var = var
-- skip-rec-subst rav = rav
-- skip-rec-subst (seq sk sk') = seq (skip-rec-subst sk) (skip-rec-subst sk')
-- skip-rec-subst (rec sk) = rec {!!}

-- diverge-rec-subst : ∀{n r s} {A : PreType n r} {τ : Fin r → PreType n s} →
--                     (∀ x → IDiverge (τ x)) → IDiverge A → IDiverge (rec-subst τ A)
-- diverge-rec-subst dτ inv = dτ _
-- diverge-rec-subst dτ (seq div) = seq (diverge-rec-subst dτ div)
-- diverge-rec-subst dτ (seqε x div) = seqε {!!} (diverge-rec-subst dτ div)
-- diverge-rec-subst dτ (rec div) = rec (diverge-rec-subst {!!} div)

-- lemma : ∀{n r} {A : PreType n r} → IDiverge A → ∞Diverge A
-- lemma inv .unbox = inv
-- lemma (seq div) .unbox = seq (lemma div)
-- lemma (seqε x div) .unbox = seqε x (lemma div)
-- lemma (rec div) .unbox = rec (lemma (diverge-rec-subst (λ { zero → rec div ; (suc x) → inv}) div))

ext∗ : ∀{r s} → (k : ℕ) → Renaming r s → Renaming (k + r) (k + s)
ext∗ zero ρ = ρ
ext∗ (suc k) ρ = ext (ext∗ k ρ)

suc+ : ∀{r} → (k : ℕ) → Renaming (k + r) (suc (k + r))
suc+ zero = suc
suc+ (suc n) = ext (suc+ n)

suc+ext∗ : ∀{r s} {ρ : Renaming r s} (k : ℕ) (x : Fin (k + r)) →
          suc+ k (ext∗ k ρ x) ≡ ext (ext∗ k ρ) (suc+ k x)
suc+ext∗ zero x = refl
suc+ext∗ (suc k) zero = refl
suc+ext∗ (suc k) (suc x) = cong suc (suc+ext∗ k x)

-- ext∗-suc-ext∗ : ∀{r s} {ρ : Renaming r s} (k : ℕ) (x : Fin (k + r)) →
--                 ext∗ k suc (ext∗ k ρ x) ≡ ext (ext∗ k ρ) (ext∗ k suc x)
-- ext∗-suc-ext∗ = ?

-- ext∗ k suc (ext∗ k ρ x) ≡ ext (ext∗ k ρ) (ext∗ k suc x)

rename-suc-rename : ∀{k n r s} (ρ : Renaming r s) (A : PreType n (k + r)) →
                    rename (suc+ k) (rename (ext∗ k ρ) A) ≡
                    rename (ext (ext∗ k ρ)) (rename (suc+ k) A)
rename-suc-rename ρ (var x) = refl
rename-suc-rename ρ (rav x) = refl
rename-suc-rename ρ skip = refl
rename-suc-rename ρ ⊤ = refl
rename-suc-rename ρ 𝟘 = refl
rename-suc-rename ρ ⊥ = refl
rename-suc-rename ρ 𝟙 = refl
rename-suc-rename ρ (A ⨟ B) = cong₂ _⨟_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (A & B) = cong₂ _&_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (A ⊕ B) = cong₂ _⊕_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (A ⅋ B) = cong₂ _⅋_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (A ⊗ B) = cong₂ _⊗_ (rename-suc-rename ρ A) (rename-suc-rename ρ B)
rename-suc-rename ρ (get x) = refl
rename-suc-rename ρ (put x) = refl
rename-suc-rename {k} ρ (inv x) = cong inv (suc+ext∗ k x)
rename-suc-rename ρ (rec A) = cong rec (rename-suc-rename ρ A)

exts∗ : ∀{n r s} → (k : ℕ) → (Unfolding n r s) → Unfolding n (k + r) (k + s)
exts∗ zero σ = σ
exts∗ (suc k) σ = exts (exts∗ k σ)

exts-rename : ∀{k n r s} (x : Fin (k + r)) (σ : Unfolding n r s) →
              exts (exts∗ k σ) (suc+ k x) ≡ rename (suc+ k) (exts∗ k σ x)
exts-rename {zero} x σ = refl
exts-rename {suc k} zero σ = refl
exts-rename {suc k} (suc x) σ = begin
  rename suc (exts (exts∗ k σ) (suc+ k x))
    ≡⟨ cong (rename suc) (exts-rename x σ) ⟩
  rename suc (rename (suc+ k) (exts∗ k σ x))
    ≡⟨ rename-suc-rename {0} (suc+ k) (exts∗ k σ x) ⟩
  rename (ext (suc+ k)) (rename suc (exts∗ k σ x))
  ∎ where open Eq.≡-Reasoning

rec-subst-rename : ∀{k n r s} (A : PreType n (k + r)) (σ : Unfolding n r s) →
                   rec-subst (exts∗ (suc k) σ) (rename (suc+ k) A) ≡
                   rename (suc+ k) (rec-subst (exts∗ k σ) A)
rec-subst-rename (var x) σ = refl
rec-subst-rename (rav x) σ = refl
rec-subst-rename skip σ = refl
rec-subst-rename ⊤ σ = refl
rec-subst-rename 𝟘 σ = refl
rec-subst-rename ⊥ σ = refl
rec-subst-rename 𝟙 σ = refl
rec-subst-rename (A ⨟ B) σ = cong₂ _⨟_ (rec-subst-rename A σ) (rec-subst-rename B σ)
rec-subst-rename (A & B) σ = cong₂ _&_ (rec-subst-rename A σ) (rec-subst-rename B σ)
rec-subst-rename (A ⊕ B) σ = cong₂ _⊕_ (rec-subst-rename A σ) (rec-subst-rename B σ)
rec-subst-rename (A ⅋ B) σ = cong₂ _⅋_ (rec-subst-rename A σ) (rec-subst-rename B σ)
rec-subst-rename (A ⊗ B) σ = cong₂ _⊗_ (rec-subst-rename A σ) (rec-subst-rename B σ)
rec-subst-rename (get x) σ = refl
rec-subst-rename (put x) σ = refl
rec-subst-rename (inv x) σ = exts-rename x σ
rec-subst-rename (rec A) σ = cong rec (rec-subst-rename A σ)

rec-subst-exts : ∀{n r s t} (τ : Unfolding n r s) (σ : Unfolding n s t) →
                 rec-subst (exts σ) ∘ exts τ ≡ exts (rec-subst σ ∘ τ)
rec-subst-exts τ σ = extensionality aux
  where
    aux : ∀ x → rec-subst (exts σ) (exts τ x) ≡ exts (rec-subst σ ∘ τ) x
    aux zero = refl
    aux (suc x) = rec-subst-rename (τ x) σ

{-# REWRITE +-suc #-}

ext∗-suc-ext∗ : ∀{r s} {ρ : Renaming r s} (k : ℕ) (x : Fin (k + r)) →
                ext∗ {s} k suc (ext∗ k ρ x) ≡ ext (ext∗ k ρ) (ext∗ {r} k suc x)
ext∗-suc-ext∗ zero x = refl
ext∗-suc-ext∗ (suc k) zero = refl
ext∗-suc-ext∗ (suc k) (suc x) = cong suc (ext∗-suc-ext∗ k x)

rec-subst-compose : ∀{n r s t} (A : PreType n r) {τ : Unfolding n r s} {σ : Unfolding n s t} →
                    rec-subst σ (rec-subst τ A) ≡ rec-subst (rec-subst σ ∘ τ) A
rec-subst-compose (var x) = refl
rec-subst-compose (rav x) = refl
rec-subst-compose skip = refl
rec-subst-compose ⊤ = refl
rec-subst-compose 𝟘 = refl
rec-subst-compose ⊥ = refl
rec-subst-compose 𝟙 = refl
rec-subst-compose (A ⨟ B) = cong₂ _⨟_ (rec-subst-compose A) (rec-subst-compose B)
rec-subst-compose (A & B) = cong₂ _&_ (rec-subst-compose A) (rec-subst-compose B)
rec-subst-compose (A ⊕ B) = cong₂ _⊕_ (rec-subst-compose A) (rec-subst-compose B)
rec-subst-compose (A ⅋ B) = cong₂ _⅋_ (rec-subst-compose A) (rec-subst-compose B)
rec-subst-compose (A ⊗ B) = cong₂ _⊗_ (rec-subst-compose A) (rec-subst-compose B)
rec-subst-compose (get x) = refl
rec-subst-compose (put x) = refl
rec-subst-compose (inv x) = refl
rec-subst-compose (rec A) {τ} {σ} = begin
  rec (rec-subst (exts σ) (rec-subst (exts τ) A)) ≡⟨ cong rec (rec-subst-compose A) ⟩
  rec (rec-subst (rec-subst (exts σ) ∘ exts τ) A) ≡⟨ cong (λ x → rec (rec-subst x A)) (rec-subst-exts τ σ) ⟩
  rec (rec-subst (exts (rec-subst σ ∘ τ)) A) ∎
  where open Eq.≡-Reasoning

exts-exts∗ : ∀{n r s} (k : ℕ) (σ : Unfolding n r s) → exts (exts∗ k σ) ≡ exts∗ k (exts σ)
exts-exts∗ zero σ = refl
exts-exts∗ (suc k) σ = cong exts (exts-exts∗ k σ)

rec-subst-exts∗ : ∀{k n r s t} (τ : Unfolding n r s) (σ : Unfolding n s t) →
                  (x : Fin (k + r)) → rec-subst (exts∗ k σ) (exts∗ k τ x) ≡ exts∗ k (rec-subst σ ∘ τ) x
rec-subst-exts∗ {zero} τ σ x = refl
rec-subst-exts∗ {suc k} τ σ x = begin
  rec-subst (exts (exts∗ k σ)) (exts (exts∗ k τ) x)
    ≡⟨ cong₂ (λ u v → rec-subst u (v x)) (exts-exts∗ k σ) (exts-exts∗ k τ) ⟩
  rec-subst (exts∗ k (exts σ)) (exts∗ k (exts τ) x)
    ≡⟨ rec-subst-exts∗ (exts τ) (exts σ) x ⟩
  exts∗ k (rec-subst (exts σ) ∘ (exts τ)) x
    ≡⟨ cong (λ u → exts∗ k u x) (rec-subst-exts τ σ) ⟩
  exts∗ k (exts (rec-subst σ ∘ τ)) x
    ≡⟨ cong (λ u → u x) (sym (exts-exts∗ k (rec-subst σ ∘ τ))) ⟩
  exts (exts∗ k (rec-subst σ ∘ τ)) x ∎
  where open Eq.≡-Reasoning

easy : ∀{k n r s t} (A : PreType n (k + r)) (τ : Unfolding n r s) (σ : Unfolding n s t) →
       rec-subst (exts∗ k σ) (rec-subst (exts∗ k τ) A) ≡
       rec-subst (exts∗ k (rec-subst σ ∘ τ)) A
easy (var x) τ σ = refl
easy (rav x) τ σ = refl
easy skip τ σ = refl
easy ⊤ τ σ = refl
easy 𝟘 τ σ = refl
easy ⊥ τ σ = refl
easy 𝟙 τ σ = refl
easy (A ⨟ B) τ σ = cong₂ _⨟_ (easy A τ σ) (easy B τ σ)
easy (A & B) τ σ = cong₂ _&_ (easy A τ σ) (easy B τ σ)
easy (A ⊕ B) τ σ = cong₂ _⊕_ (easy A τ σ) (easy B τ σ)
easy (A ⅋ B) τ σ = cong₂ _⅋_ (easy A τ σ) (easy B τ σ)
easy (A ⊗ B) τ σ = cong₂ _⊗_ (easy A τ σ) (easy B τ σ)
easy (get x) τ σ = refl
easy (put x) τ σ = refl
easy (inv x) τ σ = rec-subst-exts∗ τ σ x
easy (rec A) τ σ = cong rec (easy A τ σ)

IdentityFrom : ∀{n r} → ℕ → Unfolding n (suc r) r → Set
IdentityFrom {_} {r} k σ = (x : Fin (k + r)) → inv x ≡ exts∗ k σ (suc+ {r} k x)

identity-from-suc : ∀{k n r} (σ : Unfolding n (suc r) r) →
                    IdentityFrom k σ → IdentityFrom (suc k) σ
identity-from-suc σ iσ zero = refl
identity-from-suc σ iσ (suc x) rewrite sym (iσ x) = refl

identity-from-s-just : ∀{n r} (A : PreType n r) → IdentityFrom 0 (s-just A)
identity-from-s-just _ _ = refl

useless-rec-subst : ∀{k n r} (σ : Unfolding n (suc r) r) (A : PreType n (k + r)) →
                    IdentityFrom k σ →
                    A ≡ rec-subst (exts∗ k σ) (rename (suc+ {r} k) A)
useless-rec-subst σ (var x) iσ = refl
useless-rec-subst σ (rav x) iσ = refl
useless-rec-subst σ skip iσ = refl
useless-rec-subst σ ⊤ iσ = refl
useless-rec-subst σ 𝟘 iσ = refl
useless-rec-subst σ ⊥ iσ = refl
useless-rec-subst σ 𝟙 iσ = refl
useless-rec-subst σ (A ⨟ B) iσ = cong₂ _⨟_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (A & B) iσ = cong₂ _&_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (A ⊕ B) iσ = cong₂ _⊕_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (A ⅋ B) iσ = cong₂ _⅋_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (A ⊗ B) iσ = cong₂ _⊗_ (useless-rec-subst σ A iσ) (useless-rec-subst σ B iσ)
useless-rec-subst σ (get x) iσ = refl
useless-rec-subst σ (put x) iσ = refl
useless-rec-subst σ (inv x) iσ = iσ x
useless-rec-subst σ (rec A) iσ = cong rec (useless-rec-subst σ A (identity-from-suc σ iσ))

rec-subst-s-just : ∀{n r s} (σ : Unfolding n r s) →
                   (A : PreType n (suc r)) (x : Fin (suc r)) →
                   rec-subst σ (s-just (rec A) x) ≡
                   rec-subst (s-just (rec (rec-subst (exts σ) A))) (exts σ x)
rec-subst-s-just σ A zero = refl
rec-subst-s-just σ A (suc x) =
  useless-rec-subst
    ((s-just (rec (rec-subst (exts σ) A))))
    (σ x)
    (identity-from-s-just (rec (rec-subst (exts σ) A)))

-- rename-suc-rename : ∀{k n r s} (ρ : Renaming r s) (A : PreType n (k + r)) →
--                     rename (suc+ k) (rename (ext∗ k ρ) A) ≡
--                     rename (ext (ext∗ k ρ)) (rename (suc+ k) A)

-- rename (ext suc) (rename (ext ρ) A) ≡
-- rename (ext (ext ρ)) (rename (ext suc) A)

rename-suc-rename' : ∀{k n r s} (ρ : Renaming r s) (A : PreType n (k + r)) →
                     rename (ext∗ {s} k suc) (rename (ext∗ k ρ) A) ≡
                     rename (ext (ext∗ {r} k ρ)) (rename (ext∗ {r} k suc) A)
rename-suc-rename' ρ (var x) = refl
rename-suc-rename' ρ (rav x) = refl
rename-suc-rename' ρ skip = refl
rename-suc-rename' ρ ⊤ = refl
rename-suc-rename' ρ 𝟘 = refl
rename-suc-rename' ρ ⊥ = refl
rename-suc-rename' ρ 𝟙 = refl
rename-suc-rename' ρ (A ⨟ B) = cong₂ _⨟_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (A & B) = cong₂ _&_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (A ⊕ B) = cong₂ _⊕_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (A ⅋ B) = cong₂ _⅋_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (A ⊗ B) = cong₂ _⊗_ (rename-suc-rename' ρ A) (rename-suc-rename' ρ B)
rename-suc-rename' ρ (get x) = refl
rename-suc-rename' ρ (put x) = refl
rename-suc-rename' {k} ρ (inv x) = cong inv (ext∗-suc-ext∗ k x)
rename-suc-rename' ρ (rec A) = cong rec (rename-suc-rename' ρ A)

exts-suc : ∀{k n r s} (σ : Unfolding n r s) (x : Fin (k + r)) →
           exts (exts∗ k σ) (suc+ {r} k x) ≡ rename (suc+ {s} k) (exts∗ k σ x)
exts-suc {zero} σ x = refl
exts-suc {suc k} σ zero = refl
exts-suc {suc k} {n} {r} {s} σ (suc x) = begin
    exts (exts∗ (suc k) σ) (suc+ {r} (suc k) (suc x))
      ≡⟨⟩
    rename suc (exts (exts∗ k σ) (suc+ {r} k x))
      ≡⟨ cong (rename suc) (exts-suc σ x) ⟩
    rename suc (rename (suc+ {s} k) (exts∗ k σ x))
      ≡⟨ rename-suc-rename' {0} (suc+ {s} k) (exts∗ k σ x) ⟩
    rename (suc+ (suc k)) (exts∗ (suc k) σ (suc x)) ∎
  where open Eq.≡-Reasoning

rec-subst-exts-suc : ∀{k n r s} (σ : Unfolding n r s) (A : PreType n (k + r)) →
                     rec-subst (exts (exts∗ k σ)) (rename (suc+ {r} k) A) ≡
                     rename (suc+ {s} k) (rec-subst (exts∗ k σ) A)
rec-subst-exts-suc σ (var x) = refl
rec-subst-exts-suc σ (rav x) = refl
rec-subst-exts-suc σ skip = refl
rec-subst-exts-suc σ ⊤ = refl
rec-subst-exts-suc σ 𝟘 = refl
rec-subst-exts-suc σ ⊥ = refl
rec-subst-exts-suc σ 𝟙 = refl
rec-subst-exts-suc σ (A ⨟ B) = cong₂ _⨟_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (A & B) = cong₂ _&_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (A ⊕ B) = cong₂ _⊕_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (A ⅋ B) = cong₂ _⅋_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (A ⊗ B) = cong₂ _⊗_ (rec-subst-exts-suc σ A) (rec-subst-exts-suc σ B)
rec-subst-exts-suc σ (get x) = refl
rec-subst-exts-suc σ (put x) = refl
rec-subst-exts-suc σ (inv x) = exts-suc σ x
rec-subst-exts-suc σ (rec A) = cong rec (rec-subst-exts-suc σ A)

boh : ∀{n r s t} (σ : Unfolding n s t) (τ : Unfolding n (suc r) s) (x : Fin (suc r)) →
      rec-subst (exts σ) (exts τ (suc x)) ≡ rename suc (rec-subst σ (τ x))
boh σ τ x = rec-subst-exts-suc σ (τ x)

hard-lemma : ∀{k n r s} (σ : Unfolding n r s) →
             (A : PreType n (suc r)) (x : Fin (k + suc r)) →
             rec-subst (exts∗ k σ) (exts∗ k (s-just (rec A)) x) ≡
             rec-subst (exts∗ k (s-just (rec (rec-subst (exts σ) A)))) (exts (exts∗ k σ) x)
hard-lemma {zero} σ A x = rec-subst-s-just σ A x
hard-lemma {suc k} σ A zero = refl
hard-lemma {suc k} {_} {r} σ A (suc x) =
  let res = boh (exts∗ k (s-just (rec (rec-subst (exts σ) A)))) (exts (exts∗ k σ)) in
  begin
    rec-subst (exts∗ (suc k) σ) (exts∗ (suc k) (s-just (rec A)) (suc x))
      ≡⟨⟩
    rec-subst (exts (exts∗ k σ)) (exts (exts∗ k (s-just (rec A))) (suc x))
      ≡⟨ boh (exts∗ k σ) (exts∗ k (s-just (rec A))) x ⟩
    rename suc (rec-subst (exts∗ k σ) (exts∗ k (s-just (rec A)) x))
      ≡⟨ cong (rename suc) (hard-lemma σ A x) ⟩
    rename suc (rec-subst (exts∗ k (s-just (rec (rec-subst (exts σ) A)))) (exts (exts∗ k σ) x))
      ≡⟨ sym (boh (exts∗ k (s-just (rec (rec-subst (exts σ) A)))) (exts (exts∗ k σ)) x) ⟩
    rec-subst (exts (exts∗ k (s-just (rec (rec-subst (exts σ) A))))) (exts (exts (exts∗ k σ)) (suc x))
      ≡⟨⟩
    rec-subst (exts∗ (suc k) (s-just (rec (rec-subst (exts σ) A)))) (exts (exts∗ (suc k) σ) (suc x)) ∎
  where open Eq.≡-Reasoning

hard : ∀{k n r s} (σ : Unfolding n r s) →
       (A : PreType n (suc r)) (B : PreType n (suc k + r)) →
       rec-subst (exts∗ k σ) (rec-subst (exts∗ k (s-just (rec A))) B) ≡
       rec-subst (exts∗ k (s-just (rec (rec-subst (exts σ) A)))) (rec-subst (exts∗ (suc k) σ) B)
hard σ C (var x) = refl
hard σ C (rav x) = refl
hard σ C skip = refl
hard σ C ⊤ = refl
hard σ C 𝟘 = refl
hard σ C ⊥ = refl
hard σ C 𝟙 = refl
hard σ C (A ⨟ B) = cong₂ _⨟_ (hard σ C A) (hard σ C B)
hard σ C (A & B) = cong₂ _&_ (hard σ C A) (hard σ C B)
hard σ C (A ⊕ B) = cong₂ _⊕_ (hard σ C A) (hard σ C B)
hard σ C (A ⅋ B) = cong₂ _⅋_ (hard σ C A) (hard σ C B)
hard σ C (A ⊗ B) = cong₂ _⊗_ (hard σ C A) (hard σ C B)
hard σ C (get x) = refl
hard σ C (put x) = refl
hard σ C (inv x) = hard-lemma σ C x
hard σ C (rec B) = cong rec (hard σ C B)

rec-subst-unfold : ∀{n r s} (σ : Unfolding n r s) (A : PreType n (suc r)) →
                   rec-subst σ (unfold A) ≡ unfold (rec-subst (exts σ) A)
rec-subst-unfold σ A = hard σ A A

transitionε-rec-subst : ∀{n r s} (σ : Unfolding n r s) {A : PreType n r} →
                       A ⊨ ε ⇒ skip → rec-subst σ A ⊨ ε ⇒ skip
transitionε-rec-subst σ skip = skip
transitionε-rec-subst σ (seqε sk sk') = seqε (transitionε-rec-subst σ sk) (transitionε-rec-subst σ sk')
transitionε-rec-subst σ {rec A} (rec tr) with transitionε-rec-subst σ tr
... | tr' rewrite rec-subst-unfold σ A = rec tr'

data Empty {n r} : PreType n r → Set where
  skip : Empty skip
  seq  : ∀{A B} → Empty A → Empty B → Empty (A ⨟ B)
  rec  : ∀{A} → Empty A → Empty (rec A)

Empty-dec : ∀{n r} (A : PreType n r) → Empty A ⊎ ¬ Empty A
Empty-dec (var x) = inj₂ λ ()
Empty-dec (rav x) = inj₂ λ ()
Empty-dec skip = inj₁ skip
Empty-dec ⊤ = inj₂ λ ()
Empty-dec 𝟘 = {!!}
Empty-dec ⊥ = {!!}
Empty-dec 𝟙 = {!!}
Empty-dec (A ⨟ A₁) = {!!}
Empty-dec (A & A₁) = {!!}
Empty-dec (A ⊕ A₁) = {!!}
Empty-dec (A ⅋ A₁) = {!!}
Empty-dec (A ⊗ A₁) = {!!}
Empty-dec (get x) = {!!}
Empty-dec (put x) = inj₂ {!!}
Empty-dec (inv x) = inj₂ λ ()
Empty-dec (rec A) with Empty-dec A
... | inj₁ x = inj₁ (rec x)
... | inj₂ y = inj₂ λ { (rec x) → y x }

empty-transition : ∀{n r} {A : PreType n r} → Empty A → A ⊨ ε ⇒ skip
empty-transition skip = skip
empty-transition (seq x y) = seqε (empty-transition x) (empty-transition y)
empty-transition (rec x) with empty-transition x
... | tr = rec {!!}
