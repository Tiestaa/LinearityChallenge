{-# OPTIONS --rewriting --guardedness #-}
module Type.Transitions where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂)

open import Type

data Label : Set where
  ε ⊥ 𝟙 ⊤ 𝟘 &L &R ⊕L ⊕R ⅋L ⅋R ⊗L ⊗R : Label
  put get : ℕ → Label

dual-label : Label → Label
dual-label ε = ε
dual-label ⊥ = 𝟙
dual-label 𝟙 = ⊥
dual-label ⊤ = 𝟘
dual-label 𝟘 = ⊤
dual-label &L = ⊕L
dual-label &R = ⊕R
dual-label ⊕L = &L
dual-label ⊕R = &R
dual-label ⅋L = ⊗L
dual-label ⅋R = ⊗R
dual-label ⊗L = ⅋L
dual-label ⊗R = ⅋R
dual-label (put μ) = get μ
dual-label (get μ) = put μ

dual-label-inv : ∀{ℓ} → dual-label (dual-label ℓ) ≡ ℓ
dual-label-inv {ε} = refl
dual-label-inv {⊥} = refl
dual-label-inv {𝟙} = refl
dual-label-inv {⊤} = refl
dual-label-inv {𝟘} = refl
dual-label-inv {&L} = refl
dual-label-inv {&R} = refl
dual-label-inv {⊕L} = refl
dual-label-inv {⊕R} = refl
dual-label-inv {⅋L} = refl
dual-label-inv {⅋R} = refl
dual-label-inv {⊗L} = refl
dual-label-inv {⊗R} = refl
dual-label-inv {put μ} = refl
dual-label-inv {get μ} = refl

{-# REWRITE dual-label-inv #-}

data Special : Label → Set where
  ε  : Special ε
  ⊗L : Special ⊗L
  ⅋L : Special ⅋L

dual-special : ∀{ℓ} → Special ℓ → Special (dual-label ℓ)
dual-special ε = ε
dual-special ⊗L = ⅋L
dual-special ⅋L = ⊗L

special-decidable : (ℓ : Label) → Special ℓ ⊎ ¬ Special ℓ
special-decidable ε = inj₁ ε
special-decidable ⊥ = inj₂ λ ()
special-decidable 𝟙 = inj₂ (λ ())
special-decidable ⊤ = inj₂ λ ()
special-decidable 𝟘 = inj₂ λ ()
special-decidable &L = inj₂ λ ()
special-decidable &R = inj₂ λ ()
special-decidable ⊕L = inj₂ λ ()
special-decidable ⊕R = inj₂ λ ()
special-decidable ⅋L = inj₁ ⅋L
special-decidable ⅋R = inj₂ λ ()
special-decidable ⊗L = inj₁ ⊗L
special-decidable ⊗R = inj₂ (λ ())
special-decidable (put x) = inj₂ λ ()
special-decidable (get x) = inj₂ λ ()

not-special-not-ε : {ℓ : Label} → ¬ Special ℓ → ℓ ≢ ε
not-special-not-ε ns refl = ns ε

data _⊨_⇒_ {n r} : PreType n r → Label → PreType n r → Set where
  skip : skip ⊨ ε ⇒ skip
  ⊥    : ⊥ ⊨ ⊥ ⇒ ⊥
  𝟙    : 𝟙 ⊨ 𝟙 ⇒ 𝟙
  ⊤    : ⊤ ⊨ ⊤ ⇒ ⊤
  𝟘    : 𝟘 ⊨ 𝟘 ⇒ 𝟘
  &L   : ∀{A B} → (A & B) ⊨ &L ⇒ A
  &R   : ∀{A B} → (A & B) ⊨ &R ⇒ B
  ⊕L   : ∀{A B} → (A ⊕ B) ⊨ ⊕L ⇒ A
  ⊕R   : ∀{A B} → (A ⊕ B) ⊨ ⊕R ⇒ B
  ⅋L   : ∀{A B} → (A ⅋ B) ⊨ ⅋L ⇒ A
  ⅋R   : ∀{A B} → (A ⅋ B) ⊨ ⅋R ⇒ B
  ⊗L   : ∀{A B} → (A ⊗ B) ⊨ ⊗L ⇒ A
  ⊗R   : ∀{A B} → (A ⊗ B) ⊨ ⊗R ⇒ B
  seq  : ∀{A B C ℓ} → A ⊨ ℓ ⇒ B → ¬ Special ℓ → (A ⨟ C) ⊨ ℓ ⇒ (B ⨟ C)
  seqε : ∀{A B C ℓ} → A ⊨ ε ⇒ skip → B ⊨ ℓ ⇒ C → (A ⨟ B) ⊨ ℓ ⇒ C
  seq⊗ : ∀{A B C} → A ⊨ ⊗L ⇒ C → (A ⨟ B) ⊨ ⊗L ⇒ C
  seq⅋ : ∀{A B C} → A ⊨ ⅋L ⇒ C → (A ⨟ B) ⊨ ⅋L ⇒ C
  put  : ∀{μ} → put μ ⊨ put μ ⇒ skip
  get  : ∀{μ} → get μ ⊨ get μ ⇒ skip
  rec  : ∀{A B ℓ} → unfold A ⊨ ℓ ⇒ B → rec A ⊨ ℓ ⇒ B

only-skip : ∀{n ℓ} {A B C : Type n} → A ⊨ ε ⇒ B → A ⊨ ℓ ⇒ C → ℓ ≡ ε
only-skip skip skip = refl
only-skip (seq x xns) _ = contradiction ε xns
only-skip (seqε sk x) (seq y yns) rewrite only-skip sk y = refl
only-skip (seqε _ x) (seqε _ y) = only-skip x y
only-skip (seqε sk x) (seq⊗ y) with only-skip sk y
... | ()
only-skip (seqε sk x) (seq⅋ y) with only-skip sk y
... | ()
only-skip (rec x) (rec y) = only-skip x y

deterministic : ∀{n ℓ} {A B C : Type n} → A ⊨ ℓ ⇒ B → A ⊨ ℓ ⇒ C → B ≡ C
deterministic skip skip = refl
deterministic ⊥ ⊥ = refl
deterministic 𝟙 𝟙 = refl
deterministic ⊤ ⊤ = refl
deterministic 𝟘 𝟘 = refl
deterministic &L &L = refl
deterministic &R &R = refl
deterministic ⊕L ⊕L = refl
deterministic ⊕R ⊕R = refl
deterministic ⅋L ⅋L = refl
deterministic ⅋R ⅋R = refl
deterministic ⊗L ⊗L = refl
deterministic ⊗R ⊗R = refl
deterministic (seq x xns) (seq y yns) = cong₂ _⨟_ (deterministic x y) refl
deterministic (seq x xns) (seqε sk y) rewrite only-skip sk x = contradiction ε xns
deterministic (seq x xns) (seq⊗ y) = contradiction ⊗L xns
deterministic (seq x xns) (seq⅋ y) = contradiction ⅋L xns
deterministic (seqε sk x) (seq y yns) rewrite only-skip sk y = contradiction ε yns
deterministic (seqε _ x) (seqε _ y) = deterministic x y
deterministic (seqε sk x) (seq⊗ y) with only-skip sk y
... | ()
deterministic (seqε sk x) (seq⅋ y) with only-skip sk y
... | ()
deterministic (seq⊗ x) (seq y yns) = contradiction ⊗L yns
deterministic (seq⊗ x) (seqε sk y) with only-skip sk x
... | ()
deterministic (seq⊗ x) (seq⊗ y) = deterministic x y
deterministic (seq⅋ x) (seq y yns) = contradiction ⅋L yns
deterministic (seq⅋ x) (seqε sk y) with only-skip sk x
... | ()
deterministic (seq⅋ x) (seq⅋ y) = deterministic x y
deterministic put put = refl
deterministic get get = refl
deterministic (rec x) (rec y) = deterministic x y

afterεskip : ∀{n r} {A B : PreType n r} → A ⊨ ε ⇒ B → B ≡ skip
afterεskip skip = refl
afterεskip (seq tr x) = contradiction ε x
afterεskip (seqε sk tr) = afterεskip tr
afterεskip (rec tr) = afterεskip tr

transition-dual : ∀{n ℓ} {A B : Type n} → A ⊨ ℓ ⇒ B → dual A ⊨ dual-label ℓ ⇒ dual B
transition-dual skip = skip
transition-dual ⊥ = 𝟙
transition-dual 𝟙 = ⊥
transition-dual ⊤ = 𝟘
transition-dual 𝟘 = ⊤
transition-dual &L = ⊕L
transition-dual &R = ⊕R
transition-dual ⊕L = &L
transition-dual ⊕R = &R
transition-dual ⅋L = ⊗L
transition-dual ⅋R = ⊗R
transition-dual ⊗L = ⅋L
transition-dual ⊗R = ⅋R
transition-dual (seq x xns) = seq (transition-dual x) (contraposition dual-special xns)
transition-dual (seqε sk x) = seqε (transition-dual sk) (transition-dual x)
transition-dual (seq⊗ x) = seq⅋ (transition-dual x)
transition-dual (seq⅋ x) = seq⊗ (transition-dual x)
transition-dual put = get
transition-dual get = put
transition-dual (rec x) = rec (transition-dual x)
