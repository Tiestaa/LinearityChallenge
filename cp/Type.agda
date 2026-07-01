{-# OPTIONS --rewriting #-}
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite

{-- Using de Bruijn notation --}
data PreType : ℕ → Set where
    ⊤ 𝟘 ⊥ 𝟙         : ∀{n} → PreType n
    var rav         : ∀{n} → Fin n → PreType n
    _&_ _⊕_ _⅋_ _⊗_ : ∀{n} → PreType n → PreType n → PreType n
    `∀ `∃           : ∀{n} → PreType (suc n) → PreType n
    `! `?           : ∀{n} → PreType n → PreType n


{-- Define the dual --}
dual : ∀{n} → PreType n → PreType n
dual ⊤      = 𝟘
dual 𝟘      = ⊤
dual ⊥       = 𝟙
dual 𝟙       = ⊥
dual (var X) = rav X
dual (rav X) = var X
dual (A & B) = dual A ⊕ dual B
dual (A ⊕ B) = dual A & dual B
dual (A ⅋ B) = dual A ⊗ dual B
dual (A ⊗ B) = dual A ⅋ dual B
dual (`∀ A)  = `∃ (dual A)
dual (`∃ A)  = `∀ (dual A)
dual (`! A)  = `? (dual A)
dual (`? A)  = `! (dual A)

{-- involution proprerty proof --}
dual-inv : ∀{n} {A : PreType n} → dual (dual A) ≡ A
dual-inv {_} {⊤}    = refl
dual-inv {_} {𝟘}    = refl
dual-inv {_} {⊥}    = refl
dual-inv {_} {𝟙}     = refl
dual-inv {_} {var X} = refl
dual-inv {_} {rav X} = refl
dual-inv {_} {A & B} = cong₂ _&_ dual-inv dual-inv
dual-inv {_} {A ⊕ B} = cong₂ _⊕_ dual-inv dual-inv
dual-inv {_} {A ⅋ B} = cong₂ _⅋_ dual-inv dual-inv
dual-inv {_} {A ⊗ B} = cong₂ _⊗_ dual-inv dual-inv
dual-inv {_} {`∀ A} = cong `∀ dual-inv
dual-inv {_} {`∃ A} = cong `∃ dual-inv
dual-inv {_} {`! A} = cong `! dual-inv
dual-inv {_} {`? A} = cong `? dual-inv

{-# REWRITE dual-inv #-}


{-- extend of one variable --}
ext : ∀{m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)


{-- rename for lifting operation --}
{-- to avoid variable capture --}
rename : ∀{m n} → (Fin m → Fin n) → PreType m → PreType n
rename ρ ⊤ = ⊤
rename ρ 𝟘 = 𝟘
rename ρ ⊥ = ⊥
rename ρ 𝟙 = 𝟙
rename ρ (var x) = var (ρ x)
rename ρ (rav x) = rav (ρ x)
rename ρ (A & B) = (rename ρ A) & (rename ρ B)
rename ρ (A ⊕ B) = (rename ρ A) ⊕ (rename ρ B)
rename ρ (A ⅋ B) = (rename ρ A) ⅋ (rename ρ B)
rename ρ (A ⊗ B) = (rename ρ A) ⊗ (rename ρ B)
rename ρ (`∀ A) = `∀ (rename (ext ρ) A)
rename ρ (`∃ A) = `∃ (rename (ext ρ) A)
rename ρ (`! A) = `! (rename ρ A)
rename ρ (`? A) = `? (rename ρ A)


{-- extention or lifing --}
{-- used to map new variables --}
exts : ∀{m n} → (Fin m → PreType n) → Fin (suc m) → PreType (suc n)
exts map zero = var zero
exts map (suc k) = rename suc (map k)

{-- Substitution (Kokke et al.) --}
{-- We use a "Map" of substitution, not one at time--}
subst : ∀{m n} → (Fin m → PreType n) → PreType m → PreType n
subst {_} map ⊤ = ⊤
subst {_} map 𝟘 = 𝟘
subst {_} map ⊥ = ⊥
subst {_} map 𝟙 = 𝟙
subst {_} map (var x) = map x
subst {_} map (rav x) = dual (map x)
subst {_} map (A & B) = subst map A & subst map B
subst {_} map (A ⊕ B) = subst map A ⊕ subst map B
subst {_} map (A ⅋ B) = subst map A ⅋ subst map B
subst {_} map (A ⊗ B) = subst map A ⊗ subst map B
subst {_} map (`∀ A) = `∀ (subst (exts map) A)
subst {_} map (`∃ A) = `∃ (subst (exts map) A)
subst {_} map (`! A) = `! (subst map A)
subst {_} map (`? A) = `? (subst map A)



{-- duality preserves substitution proof --}
dual-subst : ∀{m n} {map : Fin m → PreType n} {A : PreType m} → subst map (dual A) ≡ dual (subst map A) 
dual-subst {_} {_} {map} {⊤} = refl
dual-subst {_} {_} {map} {𝟘} = refl
dual-subst {_} {_} {map} {⊥} = refl
dual-subst {_} {_} {map} {𝟙} = refl
dual-subst {_} {_} {map} {var x} = refl
dual-subst {_} {_} {map} {rav x} = refl
dual-subst {_} {_} {map} {A & B} = cong₂ _⊕_ (dual-subst {map = map} {A = A}) (dual-subst {map = map} {A = B})
dual-subst {_} {_} {map} {A ⊕ B} = cong₂ _&_ (dual-subst {map = map} {A = A}) (dual-subst {map = map} {A = B})
dual-subst {_} {_} {map} {A ⅋ B} = cong₂ _⊗_ (dual-subst {map = map} {A = A}) (dual-subst {map = map} {A = B})
dual-subst {_} {_} {map} {A ⊗ B} = cong₂ _⅋_ (dual-subst {map = map} {A = A}) (dual-subst {map = map} {A = B})
dual-subst {_} {_} {map} {`∀ A} = cong `∃ (dual-subst {map = exts map} {A = A})
dual-subst {_} {_} {map} {`∃ A} = cong `∀ (dual-subst {map = exts map} {A = A})
dual-subst {_} {_} {map} {`! A} = cong `? (dual-subst {map = map} {A = A})
dual-subst {_} {_} {map} {`? A} = cong `! (dual-subst {map = map} {A = A})

{-# REWRITE dual-subst #-}

{-- Define Type --}
Type : Set
Type = PreType zero