{-# OPTIONS --rewriting --guardedness #-}
module Type.Kind where

open import Function using (_∘_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
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

data Kind (r : ℕ) : Set where
  ∗ ε • : Kind r
  ◦     : Fin r → Kind r

data _⦂_ {n r : ℕ} : PreType n r → Kind r → Set where
  skip : skip ⦂ ε
  bot  : ⊥ ⦂ •
  one  : 𝟙 ⦂ •
  top  : ⊤ ⦂ •
  zero : 𝟘 ⦂ •
  put  : ∀{μ} → put μ ⦂ •
  get  : ∀{μ} → get μ ⦂ •
  var  : ∀{x} → var x ⦂ ε
  rav  : ∀{x} → rav x ⦂ ε
  seqε : ∀{A B k} → A ⦂ ε → B ⦂ k → (A ⨟ B) ⦂ k
  seq• : ∀{A B} → A ⦂ • → (A ⨟ B) ⦂ •
  par  : ∀{A B} → (A ⅋ B) ⦂ •
  ten  : ∀{A B} → (A ⊗ B) ⦂ •
  amp  : ∀{A B} → (A & B) ⦂ •
  plus : ∀{A B} → (A ⊕ B) ⦂ •
  rec  : ∀{A k} → unfold A ⦂ k → rec A ⦂ k

⦂ε-transition : ∀{r} {A : PreType 0 r} → A ⦂ ε → A ⊨ ε ⇒ skip
⦂ε-transition skip = skip
⦂ε-transition (seqε x y) = seqε (⦂ε-transition x) (⦂ε-transition y)
⦂ε-transition (rec x) = rec (⦂ε-transition x)

⦂•-transition : ∀{r} {A : PreType 0 r} → A ⦂ • → ∃[ ℓ ] ∃[ B ] ℓ ≢ ε × A ⊨ ℓ ⇒ B
⦂•-transition bot = _ , _ , (λ ()) , ⊥
⦂•-transition one = _ , _ , (λ ()) , 𝟙
⦂•-transition top = _ , _ , (λ ()) , ⊤
⦂•-transition zero = _ , _ , (λ ()) , 𝟘
⦂•-transition put = _ , _ , (λ ()) , put
⦂•-transition get = _ , _ , (λ ()) , get
⦂•-transition (seqε x y) with ⦂•-transition y
... | ℓ , _ , ne , tr = ℓ , _ , ne , seqε (⦂ε-transition x) tr
⦂•-transition (seq• x) with ⦂•-transition x
... | ε , _ , ne , tr = contradiction refl ne
... | ⊥ , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | 𝟙 , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | ⊤ , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | 𝟘 , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | &L , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | &R , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | ⊕L , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | ⊕R , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | ⅋L , _ , ne , tr = _ , _ , (λ ()) , seq⅋ tr
... | ⅋R , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | ⊗L , _ , ne , tr = _ , _ , (λ ()) , seq⊗ tr
... | ⊗R , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | put x₁ , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
... | get x₁ , _ , ne , tr = _ , _ , (λ ()) , seq tr λ ()
⦂•-transition par = _ , _ , (λ ()) , ⅋L
⦂•-transition ten = _ , _ , (λ ()) , ⊗L
⦂•-transition amp = _ , _ , (λ ()), &L
⦂•-transition plus = _ , _ , (λ ()) , ⊕L
⦂•-transition (rec x) with ⦂•-transition x
... | ℓ , _ , ne , tr = ℓ , _ , ne , rec tr

transition-⦂ε : ∀{n r} {A B : PreType n r} → A ⊨ ε ⇒ B → A ⦂ ε
transition-⦂ε skip = skip
transition-⦂ε (seq tr ns) = contradiction ε ns
transition-⦂ε (seqε tr tr') = seqε (transition-⦂ε tr) (transition-⦂ε tr')
transition-⦂ε (rec tr) = rec (transition-⦂ε tr)

transition-⦂ : ∀{n r ℓ} {A B : PreType n r} → A ⊨ ℓ ⇒ B → ∃[ k ] A ⦂ k
transition-⦂ skip = ε , skip
transition-⦂ ⊥ = • , bot
transition-⦂ 𝟙 = • , one
transition-⦂ ⊤ = • , top
transition-⦂ 𝟘 = • , zero
transition-⦂ &L = • , amp
transition-⦂ &R = • , amp
transition-⦂ ⊕L = • , plus
transition-⦂ ⊕R = • , plus
transition-⦂ ⅋L = • , par
transition-⦂ ⅋R = • , par
transition-⦂ ⊗L = • , ten
transition-⦂ ⊗R = • , ten
transition-⦂ (seq tr x) = {!!}
transition-⦂ (seqε tr tr₁) = {!!}
transition-⦂ (seq⊗ tr) = {!!}
transition-⦂ (seq⅋ tr) = {!!}
transition-⦂ put = • , put
transition-⦂ get = • , get
transition-⦂ (rec tr) = {!!}

⦂good-kinds : ∀{n r k} {A : PreType n r} → A ⦂ k → k ≡ ε ⊎ k ≡ •
⦂good-kinds skip = inj₁ refl
⦂good-kinds bot = inj₂ refl
⦂good-kinds one = inj₂ refl
⦂good-kinds top = inj₂ refl
⦂good-kinds zero = inj₂ refl
⦂good-kinds put = inj₂ refl
⦂good-kinds get = inj₂ refl
⦂good-kinds var = inj₁ refl
⦂good-kinds rav = inj₁ refl
⦂good-kinds (seqε x y) = ⦂good-kinds y
⦂good-kinds (seq• x) = ⦂good-kinds x
⦂good-kinds par = inj₂ refl
⦂good-kinds ten = inj₂ refl
⦂good-kinds amp = inj₂ refl
⦂good-kinds plus = inj₂ refl
⦂good-kinds (rec x) = ⦂good-kinds x

data _::_ {n r : ℕ} : PreType n r → Kind r → Set where
  skip : skip :: ε
  bot  : ⊥ :: •
  one  : 𝟙 :: •
  top  : ⊤ :: •
  zero : 𝟘 :: •
  put  : ∀{μ} → put μ :: •
  get  : ∀{μ} → get μ :: •
  var  : ∀{x} → var x :: ε
  rav  : ∀{x} → rav x :: ε
  seqε : ∀{A B k} → A :: ε → B :: k → (A ⨟ B) :: k
  seq• : ∀{A B} → A :: • → (A ⨟ B) :: •
  seq∗ : ∀{A B} → A :: ∗ → (A ⨟ B) :: ∗
  seq◦ : ∀{A B x} → A :: ◦ x → (A ⨟ B) :: ◦ x
  par  : ∀{A B} → (A ⅋ B) :: •
  ten  : ∀{A B} → (A ⊗ B) :: •
  amp  : ∀{A B} → (A & B) :: •
  plus : ∀{A B} → (A ⊕ B) :: •
  inv  : ∀ x → inv x :: ◦ x
  recε : ∀{A} → A :: ε → rec A :: ε
  rec• : ∀{A} → A :: • → rec A :: •
  rec  : ∀{A} → A :: ◦ zero → rec A :: ∗
  rec◦ : ∀{A x} → A :: ◦ (suc x) → rec A :: ◦ x
  rec∗ : ∀{A} → A :: ∗ → rec A :: ∗

unique-kind : ∀{n r k k'} {A : PreType n r} → A :: k → A :: k' → k ≡ k'
unique-kind skip skip = refl
unique-kind bot bot = refl
unique-kind one one = refl
unique-kind top top = refl
unique-kind zero zero = refl
unique-kind put put = refl
unique-kind get get = refl
unique-kind var var = refl
unique-kind rav rav = refl
unique-kind (seqε x x') (seqε y y') = unique-kind x' y'
unique-kind (seqε x x') (seq• y) with () ← unique-kind x y
unique-kind (seqε x x') (seq∗ y) with () ← unique-kind x y
unique-kind (seqε x x') (seq◦ y) with () ← unique-kind x y
unique-kind (seq• x) (seqε y y₁) with () ← unique-kind x y
unique-kind (seq• x) (seq• y) = refl
unique-kind (seq• x) (seq∗ y) = unique-kind x y
unique-kind (seq• x) (seq◦ y) = unique-kind x y
unique-kind (seq∗ x) (seqε y y₁) with () ← unique-kind x y
unique-kind (seq∗ x) (seq• y) = unique-kind x y
unique-kind (seq∗ x) (seq∗ y) = refl
unique-kind (seq∗ x) (seq◦ y) = unique-kind x y
unique-kind (seq◦ x) (seqε y y₁) with () ← unique-kind x y
unique-kind (seq◦ x) (seq• y) = unique-kind x y
unique-kind (seq◦ x) (seq∗ y) = unique-kind x y
unique-kind (seq◦ x) (seq◦ y) = unique-kind x y
unique-kind par par = refl
unique-kind ten ten = refl
unique-kind amp amp = refl
unique-kind plus plus = refl
unique-kind (inv _) (inv _) = refl
unique-kind (recε x) (recε y) = refl
unique-kind (recε x) (rec• y) with () ← unique-kind x y
unique-kind (recε x) (rec y) with () ← unique-kind x y
unique-kind (recε x) (rec◦ y) with () ← unique-kind x y
unique-kind (recε x) (rec∗ y) with () ← unique-kind x y
unique-kind (rec• x) (recε y) with () ← unique-kind x y
unique-kind (rec• x) (rec• y) = refl
unique-kind (rec• x) (rec y) with () ← unique-kind x y
unique-kind (rec• x) (rec◦ y) with () ← unique-kind x y
unique-kind (rec• x) (rec∗ y) with () ← unique-kind x y
unique-kind (rec x) (recε y) with () ← unique-kind x y
unique-kind (rec x) (rec• y) with () ← unique-kind x y
unique-kind (rec x) (rec y) = refl
unique-kind (rec x) (rec◦ y) with () ← unique-kind x y
unique-kind (rec x) (rec∗ y) = refl
unique-kind (rec◦ x) (recε y) with () ← unique-kind x y
unique-kind (rec◦ x) (rec• y) with () ← unique-kind x y
unique-kind (rec◦ x) (rec y) with () ← unique-kind x y
unique-kind (rec◦ x) (rec◦ y) with unique-kind x y
... | refl = refl
unique-kind (rec◦ x) (rec∗ y) with () ← unique-kind x y
unique-kind (rec∗ x) (recε y) with () ← unique-kind x y
unique-kind (rec∗ x) (rec• y) with () ← unique-kind x y
unique-kind (rec∗ x) (rec y) = refl
unique-kind (rec∗ x) (rec◦ y) with () ← unique-kind x y
unique-kind (rec∗ x) (rec∗ y) = refl

Kinding : ∀{n r s} → (Fin r → PreType n s) → (Fin r → Kind s) → Set
Kinding τ κ = ∀ x → τ x :: κ x

kind-rename : ∀{r s} → Renaming r s → Kind r → Kind s
kind-rename ρ ∗ = ∗
kind-rename ρ ε = ε
kind-rename ρ • = •
kind-rename ρ (◦ x) = ◦ (ρ x)

kind-subst : ∀{r s} → (Fin r → Kind s) → Kind r → Kind s
kind-subst κ ∗ = ∗
kind-subst κ ε = ε
kind-subst κ • = •
kind-subst κ (◦ x) = κ x

kind-exts : ∀{r s} → (Fin r → Kind s) → Fin (suc r) → Kind (suc s)
kind-exts κ zero = ◦ zero
kind-exts κ (suc x) = kind-rename suc (κ x)

rename-kind : ∀{n r s k} {A : PreType n r} (ρ : Renaming r s) → A :: k → rename ρ A :: kind-rename ρ k
rename-kind ρ skip = skip
rename-kind ρ bot = bot
rename-kind ρ one = one
rename-kind ρ top = top
rename-kind ρ zero = zero
rename-kind ρ put = put
rename-kind ρ get = get
rename-kind ρ var = var
rename-kind ρ rav = rav
rename-kind ρ (seqε x y) = seqε (rename-kind ρ x) (rename-kind ρ y)
rename-kind ρ (seq• x) = seq• (rename-kind ρ x)
rename-kind ρ (seq∗ x) = seq∗ (rename-kind ρ x)
rename-kind ρ (seq◦ x) = seq◦ (rename-kind ρ x)
rename-kind ρ par = par
rename-kind ρ ten = ten
rename-kind ρ amp = amp
rename-kind ρ plus = plus
rename-kind ρ (inv x) = inv (ρ x)
rename-kind ρ (recε x) = recε (rename-kind (ext ρ) x)
rename-kind ρ (rec• x) = rec• (rename-kind (ext ρ) x)
rename-kind ρ (rec x) = rec (rename-kind (ext ρ) x)
rename-kind ρ (rec◦ x) = rec◦ (rename-kind (ext ρ) x)
rename-kind ρ (rec∗ x) = rec∗ (rename-kind (ext ρ) x)

extk : ∀{n r s} {τ : Fin r → PreType n s} {κ : Fin r → Kind s} →
       Kinding τ κ → Kinding (exts τ) (kind-exts κ)
extk kind zero = inv zero
extk kind (suc x) with kind x
... | p = rename-kind suc p

kind-rename-ε : ∀{r s k} (ρ : Renaming r s) → ε ≡ kind-rename ρ k → ε ≡ k
kind-rename-ε {k = ε} ρ refl = refl

kind-rename-∗ : ∀{r s k} (ρ : Renaming r s) → ∗ ≡ kind-rename ρ k → ∗ ≡ k
kind-rename-∗ {k = ∗} ρ refl = refl

kind-rename-• : ∀{r s k} (ρ : Renaming r s) → • ≡ kind-rename ρ k → • ≡ k
kind-rename-• {k = •} ρ refl = refl

kind-rename-suc : ∀{r} {x : Fin r} {k} → ◦ (suc x) ≡ kind-rename suc k → ◦ x ≡ k
kind-rename-suc {k = ◦ x} refl = refl

kind-rename-zero : ∀{r} {k : Kind r} → ¬ ◦ zero ≡ kind-rename suc k
kind-rename-zero {k = ∗} ()
kind-rename-zero {k = ε} ()
kind-rename-zero {k = •} ()
kind-rename-zero {k = ◦ x} ()

kind-exts-zero : ∀{r s} (x : Fin (suc r)) {κ : Fin r → Kind s} → ◦ zero ≡ kind-exts κ x → x ≡ zero
kind-exts-zero zero eq = refl
kind-exts-zero (suc x) eq = contradiction eq kind-rename-zero

rec-kind-subst : ∀{n r s k} {A : PreType n r} {τ : Fin r → PreType n s} {κ : Fin r → Kind s} →
                 Kinding τ κ → A :: k →
                 (rec-subst τ A :: kind-subst κ k) ⊎ (∃[ x ] ◦ x ≡ k × ε ≡ κ x)
rec-kind-subst kind skip = inj₁ skip
rec-kind-subst kind bot = inj₁ bot
rec-kind-subst kind one = inj₁ one
rec-kind-subst kind top = inj₁ top
rec-kind-subst kind zero = inj₁ zero
rec-kind-subst kind put = inj₁ put
rec-kind-subst kind get = inj₁ get
rec-kind-subst kind var = inj₁ var
rec-kind-subst kind rav = inj₁ rav
rec-kind-subst kind (seqε p q) with rec-kind-subst kind p | rec-kind-subst kind q
... | inj₁ p' | inj₁ q' = inj₁ (seqε p' q')
... | inj₁ p' | inj₂ y = inj₂ y
rec-kind-subst kind (seq• p) with rec-kind-subst kind p
... | inj₁ p' = inj₁ (seq• p')
rec-kind-subst kind (seq∗ p) with rec-kind-subst kind p
... | inj₁ p' = inj₁ (seq∗ p')
rec-kind-subst {κ = κ} kind (seq◦ {x = x} p) with rec-kind-subst kind p
... | inj₂ y = inj₂ y
... | inj₁ p' with κ x in eq
... | ∗ = inj₁ (seq∗ p')
... | ε = inj₂ (x , refl , sym eq)
... | • = inj₁ (seq• p')
... | ◦ x = inj₁ (seq◦ p')
rec-kind-subst kind par = inj₁ par
rec-kind-subst kind ten = inj₁ ten
rec-kind-subst kind amp = inj₁ amp
rec-kind-subst kind plus = inj₁ plus
rec-kind-subst kind (inv x) = inj₁ (kind x)
rec-kind-subst kind (recε p) with rec-kind-subst (extk kind) p
... | inj₁ p' = inj₁ (recε p')
rec-kind-subst kind (rec• p) with rec-kind-subst (extk kind) p
... | inj₁ p' = inj₁ (rec• p')
rec-kind-subst kind (rec p) with rec-kind-subst (extk kind) p
... | inj₁ p' = inj₁ (rec p')
... | inj₂ (_ , refl , ())
rec-kind-subst {κ = κ} kind (rec◦ {x = x} p) with rec-kind-subst (extk kind) p
... | inj₂ (x , refl , eq) = inj₂ (_ , refl , kind-rename-ε suc eq)
... | inj₁ p' with κ x
... | ∗ = inj₁ (rec∗ p')
... | ε = inj₁ (recε p')
... | • = inj₁ (rec• p')
... | ◦ x = inj₁ (rec◦ p')
rec-kind-subst kind (rec∗ p) with rec-kind-subst (extk kind) p
... | inj₁ p' = inj₁ (rec∗ p')

k-just : ∀{r} → Kind r → Fin (suc r) → Kind r
k-just k zero = k
k-just k (suc x) = ◦ x

kinding-just : ∀{n r k} {A : PreType n r} → A :: k → Kinding (s-just A) (k-just k)
kinding-just p zero = p
kinding-just p (suc x) = inv x

kind-rec-unfold : ∀{n r k} {A : PreType n (suc r)} → rec A :: k → unfold A :: k
kind-rec-unfold (recε p) with rec-kind-subst (kinding-just (recε p)) p
... | inj₁ x = x
kind-rec-unfold (rec• p) with rec-kind-subst (kinding-just (rec• p)) p
... | inj₁ x = x
kind-rec-unfold (rec p) with rec-kind-subst (kinding-just (rec p)) p
... | inj₁ x = x
... | inj₂ (_ , refl , ())
kind-rec-unfold (rec◦ p) with rec-kind-subst (kinding-just (rec◦ p)) p
... | inj₁ x = x
... | inj₂ (_ , refl , ())
kind-rec-unfold (rec∗ p) with rec-kind-subst (kinding-just (rec∗ p)) p
... | inj₁ x = x

kind-unsubst : ∀{n r s k} (A : PreType n r) {τ : Fin r → PreType n s} {κ : Fin r → Kind s} →
               Kinding τ κ → rec-subst τ A :: k →
               (∃[ k' ] A :: k' × k ≡ kind-subst κ k') ⊎
               (∃[ x ] A :: ◦ x × ε ≡ κ x)   -- exposed k because of substitution with skip
kind-unsubst (var x) kind var = inj₁ (ε , var , refl)
kind-unsubst (rav x) kind rav = inj₁ (_ , rav , refl)
kind-unsubst skip kind skip = inj₁ (_ , skip , refl)
kind-unsubst ⊤ kind top = inj₁ (_ , top , refl)
kind-unsubst 𝟘 kind zero = inj₁ (_ , zero , refl)
kind-unsubst ⊥ kind bot = inj₁ (_ , bot , refl)
kind-unsubst 𝟙 kind one = inj₁ (_ , one , refl)
kind-unsubst (A ⨟ B) kind (seqε p q) with kind-unsubst A kind p
... | inj₁ (◦ x , p' , eq) = inj₂ (_ , seq◦ p' , eq)
... | inj₂ (x , p' , eq) = inj₂ (_ , seq◦ p' , eq)
... | inj₁ (ε , p' , refl) with kind-unsubst B kind q
... | inj₁ (k , q' , eq) = inj₁ (k , seqε p' q' , eq)
... | inj₂ (x , q' , eq) = inj₂ (_ , seqε p' q' , eq)
kind-unsubst (A ⨟ B) kind (seq• p) with kind-unsubst A kind p
... | inj₁ (• , p' , refl) = inj₁ (_ , seq• p' , refl)
... | inj₁ (◦ x , p' , eq) = inj₁ (_ , seq◦ p' , eq)
... | inj₂ (x , p' , eq) = inj₂ (x , seq◦ p' , eq)
kind-unsubst (A ⨟ B) kind (seq∗ p) with kind-unsubst A kind p
... | inj₁ (∗ , p' , refl) = inj₁ (_ , seq∗ p' , refl)
... | inj₁ (◦ x , p' , eq) = inj₁ (_ , seq◦ p' , eq)
... | inj₂ (x , p' , eq) = inj₂ (x , seq◦ p' , eq)
kind-unsubst (A ⨟ B) kind (seq◦ p) with kind-unsubst A kind p
... | inj₁ (◦ x , p' , eq) = inj₁ (_ , seq◦ p' , eq)
... | inj₂ (x , p' , eq) = inj₂ (x , seq◦ p' , eq)
kind-unsubst (A & B) kind amp = inj₁ (_ , amp , refl)
kind-unsubst (A ⊕ B) kind plus = inj₁ (_ , plus , refl)
kind-unsubst (A ⅋ B) kind par = inj₁ (_ , par , refl)
kind-unsubst (A ⊗ B) kind ten = inj₁ (_ , ten , refl)
kind-unsubst (get x) kind get = inj₁ (_ , get , refl)
kind-unsubst (put x) kind put = inj₁ (_ , put , refl)
kind-unsubst (inv x) kind p with unique-kind p (kind x)
... | eq = inj₁ (_ , inv x , eq)
kind-unsubst (rec A) kind (recε p) with kind-unsubst A (extk kind) p
... | inj₁ (ε , p' , refl) = inj₁ (_ , recε p' , refl)
... | inj₁ (◦ (suc x) , p' , eq) = inj₁ (_ , rec◦ p' , kind-rename-ε suc eq)
... | inj₂ (suc x , p' , eq) = inj₂ (_ , rec◦ p' , kind-rename-ε suc eq)
kind-unsubst (rec A) kind (rec• p) with kind-unsubst A (extk kind) p
... | inj₁ (• , p' , refl) = inj₁ (_ , rec• p' , refl)
... | inj₁ (◦ (suc x) , p' , eq) = inj₁ (_ , rec◦ p' , kind-rename-• suc eq)
... | inj₂ (suc x , p' , eq) = inj₂ (_ , rec◦ p' , kind-rename-ε suc eq)
kind-unsubst (rec A) kind (rec p) with kind-unsubst A (extk kind) p
... | inj₁ (◦ x , p' , eq) rewrite kind-exts-zero x eq = inj₁ (_ , rec p' , refl)
... | inj₂ (suc x , p' , eq) = inj₂ (_ , rec◦ p' , kind-rename-ε suc eq)
kind-unsubst (rec A) kind (rec◦ p) with kind-unsubst A (extk kind) p
... | inj₁ (◦ (suc x) , p' , eq) = inj₁ (_ , rec◦ p' , kind-rename-suc eq)
... | inj₂ (suc x , p' , eq) = inj₂ (_ , rec◦ p' , kind-rename-ε suc eq)
kind-unsubst (rec A) kind (rec∗ p) with kind-unsubst A (extk kind) p
... | inj₁ (∗ , p' , refl) = inj₁ (_ , rec∗ p' , refl)
... | inj₁ (◦ (suc x) , p' , eq) = inj₁ (_ , rec◦ p' , kind-rename-∗ suc eq)
... | inj₂ (suc x , p' , eq) = inj₂ (_ , rec◦ p' , kind-rename-ε suc eq)

rec-subst-ε : ∀{n r s} {A : PreType n r} {τ : Fin r → PreType n s} → A :: ε → rec-subst τ A ~ A
rec-subst-ε skip = skip
rec-subst-ε var = var
rec-subst-ε rav = rav
rec-subst-ε (seqε x y) = seq (rec-subst-ε x) (rec-subst-ε y)
rec-subst-ε (recε x) = rec (rec-subst-ε x)

completeness-ε : ∀{n r} {A B : PreType n r} → A ⊨ ε ⇒ B → A :: ε
completeness-ε skip = skip
completeness-ε (seq tr ns) = contradiction ε ns
completeness-ε (seqε tr tr') = seqε (completeness-ε tr) (completeness-ε tr')
completeness-ε {A = rec A} (rec tr) with completeness-ε tr
... | p with kind-unsubst A (kinding-just {!!}) p
... | x = {!!}
