{-# OPTIONS --rewriting #-}
open import Data.List.Base using (List; _∷_; []; [_]; length)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Unary 
open import Data.Nat

open import Type

Context : Set
Context = List Type

infix  4 _≃_+_

{-- Getter --}
data _∈`_ (A : Type) : Context -> Set where
    here : ∀{Γ} → A ∈` (A ∷ Γ)
    there : ∀{B Γ} → A ∈` Γ → A ∈` (B ∷ Γ)

{-- Setter --}
update : ∀{A} (Γ : Context) (B : Type) → A ∈` Γ → Context
update (_ ∷ Γ) B here      = B ∷ Γ
update (x ∷ Γ) B (there i) = x ∷ update Γ B i

{-- Deleter --}
delete : ∀{A} (Γ : Context) → A ∈` Γ → Context
delete (x ∷ Γ) here      = Γ
delete (x ∷ Γ) (there p) = x ∷ delete Γ p


{-- Context splitting --}
data _≃_+_ : Context → Context → Context → Set where
    • : [] ≃ [] + []  
    <_ : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ A ∷ Δ + Θ
    >_ : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ Δ + A ∷ Θ


{-- splitting commutativity --}
+-comm : ∀{Γ Δ Θ} → Γ ≃ Δ + Θ → Γ ≃ Θ + Δ 
+-comm •     = •
+-comm (< p) = > (+-comm p)
+-comm (> p) = < (+-comm p)


{-- splitting associativity left --}
+-assoc-l : ∀{Γ Δ Θ Δ` Θ`} → Γ ≃ Δ + Θ → Δ ≃ Δ` + Θ` → ∃[ Γ` ] Γ` ≃ Θ` + Θ × Γ ≃ Δ` + Γ`
+-assoc-l • •     = [] , • , •
+-assoc-l (< p) (< q) with +-assoc-l p q
... | _ , p` , q` = _ , p` , (< q`)
+-assoc-l (< p) (> q) with +-assoc-l p q
... | _ , p` , q` = _ , (< p`) , (> q`)
+-assoc-l (> p) q with +-assoc-l p q 
... | _ , p` , q` = _ , (> p`) , (> q`)

{-- splitting associativity right --}
+-assoc-r : ∀{Γ Δ Θ Δ` Θ`} → Γ ≃ Δ + Θ → Θ ≃ Δ` + Θ` → ∃[ Γ` ] Γ` ≃ Δ + Δ`  × Γ ≃ Γ` + Θ`
+-assoc-r p q with +-assoc-l (+-comm p) (+-comm q) 
... | _ , p` , q` = _ , +-comm p` , +-comm q`


≫ : ∀{Γ} → Γ ≃ [] + Γ
≫ {[]}    = •
≫ {_ ∷ Γ} = > ≫

≪ : ∀{Γ} → Γ ≃ Γ + []
≪ = +-comm ≫


+-empty-l : ∀{Γ Δ} → Γ ≃ [] + Δ → Γ ≡ Δ 
+-empty-l •     = refl
+-empty-l (> p) = cong (_ ∷_) (+-empty-l p)

+-empty-r : ∀{Γ Δ} → Γ ≃ Δ + [] → Γ ≡ Δ 
+-empty-r •     = refl
+-empty-r (< p) = cong (_ ∷_) (+-empty-r p)


{-- Setter length preservation --}
update-lp : ∀{Γ A} (B : Type) (i : A ∈` Γ) → length Γ ≡ length (update Γ B i)
update-lp _ here      = refl
update-lp _ (there i) = cong suc (update-lp _ i)

{-- Setter position validity --}
update-valid : ∀{Γ A B} (i : A ∈` Γ) → B ∈` (update Γ B i)
update-valid here      = here
update-valid (there i) = there (update-valid i)

{-- Locality of update left --}
≃-update-l : ∀{Γ Δ Θ A B} (i : A ∈` Δ) → Γ ≃ Δ + Θ → ∃[ Γ` ] Γ` ≃ (update Δ B i ) + Θ
≃-update-l here (< s)  = _ , (< s)
≃-update-l here (> s) with ≃-update-l here s
... | _ , p = _ , (> p)
≃-update-l (there i) (< s) with ≃-update-l i s
... | _ , p = _ , (< p)
≃-update-l (there i) (> s) with ≃-update-l (there i) s
... | _ , p = _ , (> p)

{-- Locality of update left --}
≃-update-r : ∀{Γ Δ Θ A B} (i : A ∈` Θ) → Γ ≃ Δ + Θ → ∃[ Γ` ] Γ` ≃ Δ + (update Θ B i)
≃-update-r i s with ≃-update-l i (+-comm s)
... | _ , p = _ , +-comm p

{-- lift idx from split to global--}
lift-l : ∀{Γ Δ Θ A} → Γ ≃ Δ + Θ → A ∈` Δ → A ∈` Γ
lift-l (< s) here  = here
lift-l (> s) here  = there (lift-l s here)
lift-l (< s) (there p) = there (lift-l s p)
lift-l (> s) (there p) = there (lift-l s (there p))

lift-r : ∀{Γ Δ Θ A} → Γ ≃ Δ + Θ → A ∈` Θ → A ∈` Γ
lift-r p i = lift-l (+-comm p) i

{-- delete preserves splitting --}
≃-delete-l : ∀{Γ Δ Θ A} (i : A ∈` Δ) → (p : Γ ≃ Δ + Θ) → delete Γ (lift-l p i) ≃ delete Δ i + Θ
≃-delete-l here (< p)      = p
≃-delete-l here (> p)      = > (≃-delete-l here p)
≃-delete-l (there i) (< p) = < (≃-delete-l i p)
≃-delete-l (there i) (> p) = > (≃-delete-l (there i) p)

≃-delete-r : ∀{Γ Δ Θ A} (i : A ∈` Θ) → (p : Γ ≃ Δ + Θ) → delete Γ (lift-r p i) ≃ Δ + delete Θ i
≃-delete-r i p =  +-comm (≃-delete-l i (+-comm p))

{-- Unrestricted contexts --}
data Un : Context → Set where
    un-[] : Un []
    un-∷  : ∀{Γ A} → Un Γ → Un (`? A ∷ Γ)

{-- un context remain un after deleting --}
Un-delete : ∀{Γ A} (i : A ∈` Γ) → Un Γ → Un (delete Γ i)
Un-delete here      (un-∷ u) = u
Un-delete (there i) (un-∷ u) = un-∷ (Un-delete i u)
