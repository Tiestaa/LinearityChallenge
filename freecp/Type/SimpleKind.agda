{-# OPTIONS --rewriting --guardedness #-}
module Type.SimpleKind where

open import Axioms
open import Function using (_∘_)
open import Data.Nat using (ℕ; suc; zero; _≤_; s≤s; _⊔_; _+_)
open import Data.Nat.Properties as Nat
open import Data.Fin using (Fin; suc; zero)
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

suc+ : ∀{u} → (k : ℕ) → Renaming (k + u) (suc (k + u))
suc+ zero = suc
suc+ (suc n) = ext (suc+ n)

-- suc+ k = ext∗ k suc

-- exts : ∀{n r s} → (Fin r → PreType n s) → Fin (suc r) → PreType n (suc s)
-- exts σ zero = inv zero
-- exts σ (suc k) = rename suc (σ k)

suc+ext∗ : ∀{k r s} {ρ : Renaming r s} (x : Fin (k + r)) →
          suc+ k (ext∗ k ρ x) ≡ ext (ext∗ k ρ) (suc+ k x)
suc+ext∗ {zero} x = refl
suc+ext∗ {suc k} zero = refl
suc+ext∗ {suc k} (suc x) = cong suc (suc+ext∗ {k} x)

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
rename-suc-rename {k} ρ (inv x) = cong inv (suc+ext∗ {k} x)
rename-suc-rename ρ (rec A) = cong rec (rename-suc-rename ρ A)

exts∗ : ∀{n r s} → (k : ℕ) → (Fin r → PreType n s) → Fin (k + r) → PreType n (k + s)
exts∗ zero σ = σ
exts∗ (suc k) σ = exts (exts∗ k σ)

exts-rename : ∀{k n r s} (x : Fin (k + r)) (σ : Fin r → PreType n s) →
              exts (exts∗ k σ) (suc+ k x) ≡ rename (suc+ k) (exts∗ k σ x)
exts-rename {zero} x σ = refl
exts-rename {suc k} zero σ = refl
exts-rename {suc k} (suc x) σ with exts-rename {k} x σ
... | eq = begin
             rename suc (exts (exts∗ k σ) (suc+ k x)) ≡⟨ cong (rename suc) eq ⟩
             rename suc (rename (suc+ k) (exts∗ k σ x)) ≡⟨ rename-suc-rename {0} (suc+ k) (exts∗ k σ x) ⟩
             rename (ext (suc+ k)) (rename suc (exts∗ k σ x)) ∎
  where open Eq.≡-Reasoning

abra : ∀{k n r s} (A : PreType n (k + r)) (σ : Fin r → PreType n s) →
       rec-subst (exts∗ (suc k) σ) (rename (suc+ k) A) ≡ rename (suc+ k) (rec-subst (exts∗ k σ) A)
abra (var x) σ = refl
abra (rav x) σ = refl
abra skip σ = refl
abra ⊤ σ = refl
abra 𝟘 σ = refl
abra ⊥ σ = refl
abra 𝟙 σ = refl
abra {k} (A ⨟ B) σ = cong₂ _⨟_ (abra {k} A σ) (abra {k} B σ)
abra {k} (A & B) σ = cong₂ _&_ (abra {k} A σ) (abra {k} B σ)
abra {k} (A ⊕ B) σ = cong₂ _⊕_ (abra {k} A σ) (abra {k} B σ)
abra {k} (A ⅋ B) σ = cong₂ _⅋_ (abra {k} A σ) (abra {k} B σ)
abra {k} (A ⊗ B) σ = cong₂ _⊗_ (abra {k} A σ) (abra {k} B σ)
abra (get x) σ = refl
abra (put x) σ = refl
abra {k} (inv x) σ = exts-rename x σ
abra {k} (rec A) σ = cong rec (abra A σ)

rec-subst-rename : ∀{n r s t} (x : Fin r) (τ : Fin r → PreType n s) (σ : Fin s → PreType n t) →
                   rec-subst (exts σ) (rename suc (τ x)) ≡
                   rename suc (rec-subst σ (τ x))
rec-subst-rename x τ σ = abra {0} (τ x) σ

rec-subst-exts : ∀{n r s t} (τ : Fin r → PreType n s) (σ : Fin s → PreType n t) →
                 rec-subst (exts σ) ∘ exts τ ≡ exts (rec-subst σ ∘ τ)
rec-subst-exts {n} {r} τ σ = extensionality aux
  where
    aux : (x : Fin (suc r)) → rec-subst (exts σ) (exts τ x) ≡ exts (rec-subst σ ∘ τ) x
    aux zero = refl
    aux (suc x) = rec-subst-rename x τ σ

rec-subst-compose : ∀{n r s t} (A : PreType n r) (τ : Fin r → PreType n s) (σ : Fin s → PreType n t) →
                    rec-subst σ (rec-subst τ A) ≡ rec-subst (rec-subst σ ∘ τ) A
rec-subst-compose (var x) τ σ = refl
rec-subst-compose (rav x) τ σ = refl
rec-subst-compose skip τ σ = refl
rec-subst-compose ⊤ τ σ = refl
rec-subst-compose 𝟘 τ σ = refl
rec-subst-compose ⊥ τ σ = refl
rec-subst-compose 𝟙 τ σ = refl
rec-subst-compose (A ⨟ B) τ σ = cong₂ _⨟_ (rec-subst-compose A τ σ) (rec-subst-compose B τ σ)
rec-subst-compose (A & B) τ σ = cong₂ _&_ (rec-subst-compose A τ σ) (rec-subst-compose B τ σ)
rec-subst-compose (A ⊕ B) τ σ = cong₂ _⊕_ (rec-subst-compose A τ σ) (rec-subst-compose B τ σ)
rec-subst-compose (A ⅋ B) τ σ = cong₂ _⅋_ (rec-subst-compose A τ σ) (rec-subst-compose B τ σ)
rec-subst-compose (A ⊗ B) τ σ = cong₂ _⊗_ (rec-subst-compose A τ σ) (rec-subst-compose B τ σ)
rec-subst-compose (get x) τ σ = refl
rec-subst-compose (put x) τ σ = refl
rec-subst-compose (inv x) τ σ = refl
rec-subst-compose (rec A) τ σ = begin
  rec (rec-subst (exts σ) (rec-subst (exts τ) A)) ≡⟨ cong rec (rec-subst-compose A (exts τ) (exts σ)) ⟩
  rec (rec-subst (rec-subst (exts σ) ∘ exts τ) A) ≡⟨ cong (λ x → rec (rec-subst x A)) (rec-subst-exts τ σ) ⟩
  rec (rec-subst (exts (rec-subst σ ∘ τ)) A) ∎
  where open Eq.≡-Reasoning
