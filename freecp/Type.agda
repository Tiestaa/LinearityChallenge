{-# OPTIONS --rewriting --guardedness #-}
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite

data PreType (n r : ℕ) : Set where
  var rav              : Fin n → PreType n r
  skip ⊤ 𝟘 ⊥ 𝟙         : PreType n r
  _⨟_ _&_ _⊕_ _⅋_ _⊗_  : PreType n r → PreType n r → PreType n r
  get put              : ℕ → PreType n r
  inv                  : Fin r → PreType n r
  rec                  : PreType n (suc r) → PreType n r

dual : ∀{n r} → PreType n r → PreType n r
dual (var x) = rav x
dual (rav x) = var x
dual ⊤       = 𝟘
dual 𝟘       = ⊤
dual ⊥       = 𝟙
dual 𝟙       = ⊥
dual (A & B) = dual A ⊕ dual B
dual (A ⊕ B) = dual A & dual B
dual (A ⅋ B) = dual A ⊗ dual B
dual (A ⊗ B) = dual A ⅋ dual B
dual skip    = skip
dual (A ⨟ B) = dual A ⨟ dual B
dual (get μ) = put μ
dual (put μ) = get μ
dual (inv x) = inv x
dual (rec A) = rec (dual A)

dual-inv : ∀{n r} {A : PreType n r} → dual (dual A) ≡ A
dual-inv {_} {_} {var x} = refl
dual-inv {_} {_} {rav x} = refl
dual-inv {_} {_} {skip} = refl
dual-inv {_} {_} {⊤} = refl
dual-inv {_} {_} {𝟘} = refl
dual-inv {_} {_} {⊥} = refl
dual-inv {_} {_} {𝟙} = refl
dual-inv {_} {_} {A ⨟ B} = cong₂ _⨟_ dual-inv dual-inv
dual-inv {_} {_} {A & B} = cong₂ _&_ dual-inv dual-inv
dual-inv {_} {_} {A ⊕ B} = cong₂ _⊕_ dual-inv dual-inv
dual-inv {_} {_} {A ⅋ B} = cong₂ _⅋_ dual-inv dual-inv
dual-inv {_} {_} {A ⊗ B} = cong₂ _⊗_ dual-inv dual-inv
dual-inv {_} {_} {get μ} = refl
dual-inv {_} {_} {put μ} = refl
dual-inv {_} {_} {inv x} = refl
dual-inv {_} {_} {rec A} = cong rec dual-inv

{-# REWRITE dual-inv #-}

Type : ℕ → Set
Type n = PreType n 0

void : ∀{n} → Type n
void = rec (inv zero)
