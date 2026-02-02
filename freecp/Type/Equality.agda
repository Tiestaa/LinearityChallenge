{-# OPTIONS --rewriting --guardedness #-}
module Type.Equality where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties as Nat
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties as Fin
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂; sym)
open import Relation.Binary.HeterogeneousEquality as Heq using (_≅_; refl)
open import Agda.Builtin.Equality.Rewrite

open import Axioms
open import Type.Base
open import Type.Renaming

data _~_ {n r s} : PreType n r → PreType n s → Set where
  skip : skip ~ skip
  bot  : ⊥ ~ ⊥
  one  : 𝟙 ~ 𝟙
  top  : ⊤ ~ ⊤
  zero : 𝟘 ~ 𝟘
  put  : ∀{μ} → put μ ~ put μ
  get  : ∀{μ} → get μ ~ get μ
  var  : ∀{x} → var x ~ var x
  rav  : ∀{x} → rav x ~ rav x
  seq  : ∀{A A' B B'} → A ~ A' → B ~ B' → (A ⨟ B) ~ (A' ⨟ B')
  par  : ∀{A A' B B'} → A ~ A' → B ~ B' → (A ⅋ B) ~ (A' ⅋ B')
  ten  : ∀{A A' B B'} → A ~ A' → B ~ B' → (A ⊗ B) ~ (A' ⊗ B')
  amp  : ∀{A A' B B'} → A ~ A' → B ~ B' → (A & B) ~ (A' & B')
  plus : ∀{A A' B B'} → A ~ A' → B ~ B' → (A ⊕ B) ~ (A' ⊕ B')
  inv  : ∀{x y} → toℕ x ≡ toℕ y → inv x ~ inv y
  rec  : ∀{A A'} → A ~ A' → rec A ~ rec A'

~refl : ∀{n r} {A : PreType n r} → A ~ A
~refl {A = var x} = var
~refl {A = rav x} = rav
~refl {A = skip} = skip
~refl {A = ⊤} = top
~refl {A = 𝟘} = zero
~refl {A = ⊥} = bot
~refl {A = 𝟙} = one
~refl {A = A ⨟ A₁} = seq ~refl ~refl
~refl {A = A & A₁} = amp ~refl ~refl
~refl {A = A ⊕ A₁} = plus ~refl ~refl
~refl {A = A ⅋ A₁} = par ~refl ~refl
~refl {A = A ⊗ A₁} = ten ~refl ~refl
~refl {A = get x} = get
~refl {A = put x} = put
~refl {A = inv x} = inv refl
~refl {A = rec A} = rec ~refl

~sym : ∀{n r s} {A : PreType n r} {B : PreType n s} → A ~ B → B ~ A
~sym skip = skip
~sym bot = bot
~sym one = one
~sym top = top
~sym zero = zero
~sym put = put
~sym get = get
~sym var = var
~sym rav = rav
~sym (seq x x₁) = seq (~sym x) (~sym x₁)
~sym (par x x₁) = par (~sym x) (~sym x₁)
~sym (ten x x₁) = ten (~sym x) (~sym x₁)
~sym (amp x x₁) = amp (~sym x) (~sym x₁)
~sym (plus x x₁) = plus (~sym x) (~sym x₁)
~sym (inv x) = inv (sym x)
~sym (rec x) = rec (~sym x)

~trans : ∀{n r s t} {A : PreType n r} {B : PreType n s} {C : PreType n t} →
          A ~ B → B ~ C → A ~ C
~trans skip skip = skip
~trans bot bot = bot
~trans one one = one
~trans top top = top
~trans zero zero = zero
~trans put put = put
~trans get get = get
~trans var var = var
~trans rav rav = rav
~trans (seq x x₁) (seq y y₁) = seq (~trans x y) (~trans x₁ y₁)
~trans (par x x₁) (par y y₁) = par (~trans x y) (~trans x₁ y₁)
~trans (ten x x₁) (ten y y₁) = ten (~trans x y) (~trans x₁ y₁)
~trans (amp x x₁) (amp y y₁) = amp (~trans x y) (~trans x₁ y₁)
~trans (plus x x₁) (plus y y₁) = plus (~trans x y) (~trans x₁ y₁)
~trans (inv x) (inv y) = inv (Eq.trans x y)
~trans (rec x) (rec y) = rec (~trans x y)

~≡ : ∀{n r} {A B : PreType n r} → A ~ B → A ≡ B
~≡ skip = refl
~≡ bot = refl
~≡ one = refl
~≡ top = refl
~≡ zero = refl
~≡ put = refl
~≡ get = refl
~≡ var = refl
~≡ rav = refl
~≡ (seq x y) = cong₂ _⨟_ (~≡ x) (~≡ y)
~≡ (par x y) = cong₂ _⅋_ (~≡ x) (~≡ y)
~≡ (ten x y) = cong₂ _⊗_ (~≡ x) (~≡ y)
~≡ (amp x y) = cong₂ _&_ (~≡ x) (~≡ y)
~≡ (plus x y) = cong₂ _⊕_ (~≡ x) (~≡ y)
~≡ (inv x) = cong inv (toℕ-injective x)
~≡ (rec x) = cong rec (~≡ x)

SameRenaming : ∀{r r' s s'} (ρ : Renaming r s) (ρ' : Renaming r' s') → Set
SameRenaming ρ ρ' = ∀{x y} → toℕ x ≡ toℕ y → toℕ (ρ x) ≡ toℕ (ρ' y)

same-ext : ∀{r r' s s'} (ρ : Renaming r s) (ρ' : Renaming r' s') →
           SameRenaming ρ ρ' → SameRenaming (ext ρ) (ext ρ')
same-ext ρ ρ' same {zero} {zero} refl = refl
same-ext ρ ρ' same {suc x} {suc y} eq = cong suc (same (Nat.suc-injective eq))

~rename : ∀{n r s r' s'} {A : PreType n r} {B : PreType n r'}
           (ρ : Renaming r s) (ρ' : Renaming r' s') → SameRenaming ρ ρ' →
           A ~ B → rename ρ A ~ rename ρ' B
~rename ρ ρ' same skip = skip
~rename ρ ρ' same bot = bot
~rename ρ ρ' same one = one
~rename ρ ρ' same top = top
~rename ρ ρ' same zero = zero
~rename ρ ρ' same put = put
~rename ρ ρ' same get = get
~rename ρ ρ' same var = var
~rename ρ ρ' same rav = rav
~rename ρ ρ' same (seq x y) = seq (~rename ρ ρ' same x) (~rename ρ ρ' same y)
~rename ρ ρ' same (par x y) = par (~rename ρ ρ' same x) (~rename ρ ρ' same y)
~rename ρ ρ' same (ten x y) = ten (~rename ρ ρ' same x) (~rename ρ ρ' same y)
~rename ρ ρ' same (amp x y) = amp (~rename ρ ρ' same x) (~rename ρ ρ' same y)
~rename ρ ρ' same (plus x y) = plus (~rename ρ ρ' same x) (~rename ρ ρ' same y)
~rename ρ ρ' same (inv x) = inv (same x)
~rename ρ ρ' same (rec x) = rec (~rename (ext ρ) (ext ρ') (same-ext ρ ρ' same) x)
