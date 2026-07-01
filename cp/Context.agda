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
infixr 9 _∗_

{-- Getter --}

data _∈`_ (A : Type) : Context -> Set where
    here : ∀{Γ} → A ∈` (A ∷ Γ)
    there : ∀{B Γ} → A ∈` Γ → A ∈` (B ∷ Γ)

{-- example --}
_ : ∀ {A B C D : Type} → C ∈` (A ∷ B ∷ C ∷ D ∷ [])
_ = there (there here)


{-- Setter --}
update : ∀{A} (Γ : Context) (B : Type) → A ∈` Γ → Context
update (_ ∷ Γ) B here      = B ∷ Γ
update (x ∷ Γ) B (there i) = x ∷ update Γ B i


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


{-- Utils --}
≫ : ∀{Γ} → Γ ≃ [] + Γ
≫ {[]}    = •
≫ {_ ∷ Γ} = > ≫

≪ : ∀{Γ} → Γ ≃ Γ + []
≪ = +-comm ≫

{-- empty left --}
+-empty-l : ∀{Γ Δ} → Γ ≃ [] + Δ → Γ ≡ Δ 
+-empty-l •     = refl
+-empty-l (> p) = cong (_ ∷_) (+-empty-l p)

{-- empty right --}
+-empty-r : ∀{Γ Δ} → Γ ≃ Δ + [] → Γ ≡ Δ 
+-empty-r •     = refl
+-empty-r (< p) = cong (_ ∷_) (+-empty-r p)


{-- Separating Conjuction --}
data _∗_ (P Q : Pred Context _) (Γ : Context) : Set where
    _〈_〉_ : ∀{Δ Θ} → P Δ → Γ ≃ Δ + Θ → Q Θ → (P ∗ Q) Γ

{-- Separating conjunction commutativity --}
∗-comm : ∀{P Q} → ∀[ P ∗ Q ⇒ Q ∗ P ]
∗-comm (p 〈 Γ 〉 q) = q 〈 +-comm Γ 〉 p

{-- Separating conjunction associativity left --}
∗-assoc-l : ∀{P Q R} → ∀[ (P ∗ Q) ∗ R ⇒ P ∗ (Q ∗ R) ]
∗-assoc-l ((p 〈 Γ 〉 q) 〈  Γ` 〉 r) with +-assoc-l Γ` Γ
... | _ , sΓ` , sΓ = p 〈 sΓ 〉 (q 〈  sΓ`  〉 r)


{-- Setter length preservation --}
update-lp : ∀{Γ A} (B : Type) (i : A ∈` Γ) → length Γ ≡ length (update Γ B i)
update-lp _ here      = refl
update-lp _ (there i) = cong suc (update-lp _ i)

{-- Setter position validity --}
update-valid : ∀{Γ A B} (i : A ∈` Γ) → B ∈` (update Γ B i)
update-valid here      = here
update-valid (there i) = there (update-valid i)

{-- Locality of update left --}
update-local-l : ∀{Γ Δ Θ A B} (i : A ∈` Δ) → Γ ≃ Δ + Θ → ∃[ Γ` ] Γ` ≃ (update Δ B i ) + Θ
update-local-l here (< s)  = _ , (< s)
update-local-l here (> s) with update-local-l here s
... | _ , p = _ , (> p)
update-local-l (there i) (< s) with update-local-l i s
... | _ , p = _ , (< p)
update-local-l (there i) (> s) with update-local-l (there i) s
... | _ , p = _ , (> p)

{-- Locality of update left --}
update-local-r : ∀{Γ Δ Θ A B} (i : A ∈` Θ) → Γ ≃ Δ + Θ → ∃[ Γ` ] Γ` ≃ Δ + (update Θ B i)
update-local-r i s with update-local-l i (+-comm s)
... | _ , p = _ , +-comm p