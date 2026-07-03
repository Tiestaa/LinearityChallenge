{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}
open import Data.List.Base using (List; _∷_; []; [_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)

open import Type
open import Context

data _↭_ : Context → Context → Set where
    refl  : ∀{Γ} → Γ ↭ Γ
    swap  : ∀{A B Γ} → (A ∷ B ∷ Γ) ↭ (B ∷ A ∷ Γ)
    prep  : ∀{A Γ Δ} → Γ ↭ Δ → (A ∷ Γ) ↭ (A ∷ Δ)
    trans : ∀{Γ Δ Θ} → Γ ↭ Δ → Δ ↭ Θ → Γ ↭ Θ

↭sym : ∀{Γ Δ} → Γ ↭ Δ → Δ ↭ Γ
↭sym refl        = refl
↭sym swap        = swap
↭sym (prep p)    = prep (↭sym p)
↭sym (trans p q) = trans (↭sym q) (↭sym p)

↭empty-inv : ∀{Γ} → Γ ↭ [] → Γ ≡ []
↭empty-inv refl        = refl
↭empty-inv (trans p q) with ↭empty-inv q
... | refl = ↭empty-inv p


↭solo-inv : ∀{A Γ} → [ A ] ↭ Γ → Γ ≡ [ A ] 
↭solo-inv refl        = refl
↭solo-inv (prep p) with ↭empty-inv (↭sym p)
... | refl = refl
↭solo-inv (trans p q) with ↭solo-inv p
... | refl = ↭solo-inv q

{-- split and permutations relation --}
↭split : ∀{Γ Γ₁ Γ₂ Δ} → Γ ↭ Δ → Γ ≃ Γ₁ + Γ₂ → ∃[ Δ₁ ] ∃[ Δ₂ ] ( Δ ≃ Δ₁ + Δ₂ × Γ₁ ↭ Δ₁ × Γ₂ ↭ Δ₂ )
↭split refl •                = _ , _ , • , refl , refl
↭split refl (< s)            = _ , _ , < s , prep refl , refl
↭split refl (> s)            = _ , _ , > s , refl , prep refl
↭split swap (< < s)          = _ , _ , < < s , swap , refl
↭split swap (< > s)          = _ , _ , > < s , refl , refl
↭split swap (> < s)          = _ , _ , < > s , refl , refl
↭split swap (> > s)          = _ , _ , (> > s) , refl , swap
↭split (prep p) (< s) with ↭split p s
... | Δ₁ , Δ₂ , s` , p₁ , p₂ =  _ ∷ Δ₁ , Δ₂ , (< s`) , prep p₁ , p₂
↭split (prep p) (> s) with ↭split p s
... | Δ₁ , Δ₂ , s` , p₁ , p₂ =  Δ₁ , _ ∷ Δ₂ , (> s`) , p₁ , prep p₂
↭split (trans p q) s with ↭split p s
... | Θ₁ , Θ₂ , s` , p₁ , p₂ with ↭split q s`
... | Δ₁ , Δ₂ , s`` , q₁ , q₂ = Δ₁ , Δ₂ , s`` , trans p₁ q₁ , trans p₂ q₂ 

↭solo : ∀{A Γ Γ` Δ}→ Γ ↭ Δ → Γ ≃ [ A ] + Γ` → ∃[ Δ` ] (Δ ≃ [ A ] + Δ` × Γ` ↭ Δ`)
↭solo π s with ↭split π s
... | _ , _ , s₁ , π₁ , π₂ with ↭solo-inv π₁
... | refl = _ , s₁ , π₂



{--  --}
↭-delete : ∀ {Γ Δ A} → Γ ↭ Δ → (i : A ∈` Γ) → (j : A ∈` Δ) → delete Γ i ↭ delete Δ j
↭-delete = {!   !}