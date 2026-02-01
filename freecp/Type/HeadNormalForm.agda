{-# OPTIONS --rewriting --guardedness #-}
module Type.HeadNormalForm where

open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
open import Agda.Builtin.Equality.Rewrite

open import Axioms
open import Type
open import Type.Equality
open import Type.Unfolding
open import Type.Equivalence
open import Type.Substitution
open import Type.Kind
open import Type.Transitions

data Visible {n} (A : Type n) : Set where
  visible : ∀{m ℓ B} (σ : Substitution n m) → subst σ A ⊨ ℓ ⇒ B → Visible A

data HeadNormalForm {n} : Type n → Set where
  null : HeadNormalForm void
  skip : HeadNormalForm skip
  bot  : HeadNormalForm ⊥
  one  : HeadNormalForm 𝟙
  top  : HeadNormalForm ⊤
  zero : HeadNormalForm 𝟘
  put  : ∀{A μ} → HeadNormalForm (put μ ⨟ A)
  get  : ∀{A μ} → HeadNormalForm (get μ ⨟ A)
  var  : ∀{A x} → HeadNormalForm (var x ⨟ A)
  rav  : ∀{A x} → HeadNormalForm (rav x ⨟ A)
  par  : ∀{A B} → HeadNormalForm (A ⅋ B)
  ten  : ∀{A B} → HeadNormalForm (A ⊗ B)
  amp  : ∀{A B} → HeadNormalForm (A & B)
  plus : ∀{A B} → HeadNormalForm (A ⊕ B)

nf-seq : ∀{n} {A B : Type n} → HeadNormalForm A → A ≡ skip ⊎ ∃[ N ] HeadNormalForm N × (A ⨟ B) ≈ N
nf-seq null = inj₂ (void , null , void⨟A≈void)
nf-seq skip = inj₁ refl
nf-seq bot = inj₂ (_ , bot , ≈⊥)
nf-seq one = inj₂ (_ , one , ≈𝟙)
nf-seq top = inj₂ (_ , top , ≈⊤)
nf-seq zero = inj₂ (_ , zero , ≈𝟘)
nf-seq put = inj₂ (_ , put , ≈sym ≈assoc)
nf-seq get = inj₂ (_ , get , ≈sym ≈assoc)
nf-seq var = inj₂ (_ , var , ≈sym ≈assoc)
nf-seq rav = inj₂ (_ , rav , ≈sym ≈assoc)
nf-seq par = inj₂ (_ , par , ≈⅋⨟)
nf-seq ten = inj₂ (_ , ten , ≈⊗⨟)
nf-seq amp = inj₂ (_ , amp , ≈dist&)
nf-seq plus = inj₂ (_ , plus , ≈dist⊕)

skip-transition : ∀{m n ℓ B} {A : Type m} (σ : Substitution m n) →
                  A ≈ skip → subst σ A ⊨ ℓ ⇒ B → ℓ ≡ ε
skip-transition σ eq tr with eq .from σ .Sim.next skip
... | _ , tr' , _ = only-skip tr' tr

nf-transition : ∀{m n ℓ B} (A : Type m) (σ : Substitution m n) →
                subst σ A ⊨ ℓ ⇒ B → ∃[ N ] HeadNormalForm N × A ≈ N
nf-transition (var x) σ tr = _ , var , A≈A⨟skip
nf-transition (rav x) σ tr = _ , rav , A≈A⨟skip
nf-transition skip σ tr = _ , skip , ≈refl
nf-transition ⊤ σ tr = _ , top , ≈refl
nf-transition 𝟘 σ tr = _ , zero , ≈refl
nf-transition ⊥ σ tr = _ , bot , ≈refl
nf-transition 𝟙 σ tr = _ , one , ≈refl
nf-transition (A ⨟ B) σ (seq tr ns) with nf-transition A σ tr
... | N , anf , aeq with nf-seq anf
... | inj₂ (N' , nf , eq) = N' , nf , ≈trans (≈cong⨟ aeq ≈refl) eq
... | inj₁ refl with skip-transition σ aeq tr
... | refl = contradiction ε ns
nf-transition (A ⨟ B) σ (seqε sk tr) with nf-transition A σ sk
... | _ , anf , aeq with nf-seq anf
... | inj₂ (_ , nf , eq) = _ , nf , ≈trans (≈cong⨟ aeq ≈refl) eq
... | inj₁ refl with nf-transition B σ tr
... | _ , bnf , beq = _ , bnf , ≈trans (≈cong⨟ aeq beq) (≈sym A≈skip⨟A)
nf-transition (A ⨟ B) σ (seq⊗ tr) with nf-transition A σ tr
... | _ , anf , aeq with nf-seq anf
... | inj₂ (_ , nf , eq) = _ , nf , ≈trans (≈cong⨟ aeq ≈refl) eq
... | inj₁ refl with skip-transition σ aeq tr
... | ()
nf-transition (A ⨟ B) σ (seq⅋ tr) with nf-transition A σ tr
... | _ , anf , aeq with nf-seq anf
... | inj₂ (_ , nf , eq) = _ , nf , ≈trans (≈cong⨟ aeq ≈refl) eq
... | inj₁ refl with skip-transition σ aeq tr
... | ()
nf-transition (A & B) σ tr = _ , amp , ≈refl
nf-transition (A ⊕ B) σ tr = _ , plus , ≈refl
nf-transition (A ⅋ B) σ tr = _ , par , ≈refl
nf-transition (A ⊗ B) σ tr = _ , ten , ≈refl
nf-transition (get x) σ tr = _ , get , A≈A⨟skip
nf-transition (put x) σ tr = _ , put , A≈A⨟skip
nf-transition (rec A) σ (rec tr)
  rewrite unfold-subst σ A with nf-transition (unfold A) σ tr
... | N , nf , eq = N , nf , ≈trans ≈rec eq

nf-visible : ∀{n} (A : Type n) → Visible A → ∃[ N ] HeadNormalForm N × A ≈ N
nf-visible A (visible σ tr) = nf-transition A σ tr

nf-invisible : ∀{n} {A : Type n} → ¬ Visible A → A ≈ void
nf-invisible nv .to σ .Sim.next tr = contradiction (visible σ tr) nv
nf-invisible nv .from σ .Sim.next tr = contradiction tr void-no-transitions

visible-decidable-visible : ∀{n} (A : Type n) → kind A ≢ ∗ → Visible A
visible-decidable-visible A ne with kind-sound A ne
... | σ , ℓ , B , tr = visible σ tr

visible-decidable-invisible : ∀{n} (A : Type n) → kind A ≡ ∗ → ¬ Visible A
visible-decidable-invisible {n} A eq (visible {m} σ tr) with transition-subst {n = 0} action-subst tr
... | tr' rewrite subst-compose {n} {m} {0} σ action-subst A with kind-complete A (action-subst · σ) tr'
... | ne = ne eq

ast-or-not : ∀{n} (k : Kind n) → k ≡ ∗ ⊎ k ≢ ∗
ast-or-not ε = inj₂ (λ ())
ast-or-not • = inj₂ (λ ())
ast-or-not ∗ = inj₁ refl
ast-or-not (var x k) = inj₂ (λ ())

visible-decidable : ∀{n} (A : Type n) → Visible A ⊎ ¬ Visible A
visible-decidable A with ast-or-not (kind A)
... | inj₁ eq = inj₂ (visible-decidable-invisible A eq)
... | inj₂ ne = inj₁ (visible-decidable-visible A ne)

head-normal-form : ∀{n} (A : Type n) → ∃[ N ] HeadNormalForm N × A ≈ N
head-normal-form A with visible-decidable A
... | inj₁ vis = nf-visible A vis
... | inj₂ nv = _ , null , nf-invisible nv
