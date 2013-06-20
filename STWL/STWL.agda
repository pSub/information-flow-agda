open import Level
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties hiding (≤-step)
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core

module STWL (Var : Set) (_==_ : Var → Var → Bool) where

data AExp : Set where
  var : Var → AExp
  num : ℕ → AExp
  opa : AExp → AExp → AExp

data BExp : Set where
  true : BExp
  false : BExp
  ¬ : BExp → BExp
  opb : BExp → BExp → BExp
  opr : AExp → AExp → BExp

data Exp : Set where
  skip : Exp
  ass : Var → AExp → Exp
  comp : Exp → Exp → Exp
  if_then_else_fi : BExp → Exp → Exp → Exp
  while_do_od : BExp → Exp → Exp

data Stop : Set where
  [] : Stop

State = Var → ℕ
Config = (Exp ⊎ Stop)  × State

data _⇓₁_ : AExp × State → ℕ → Set where
  var : ∀ x σ → (var x , σ) ⇓₁ σ x
  num : ∀ n σ → (num n , σ) ⇓₁ n
  op : ∀ a₁ a₂ σ n m → (a₁ , σ) ⇓₁ n → (a₂ , σ) ⇓₁ m → (opa a₁ a₂ , σ) ⇓₁ m

data _⇓₂_ : BExp × State → Bool → Set where
  true : ∀ σ → (true , σ) ⇓₂ true
  false : ∀ σ → (false , σ) ⇓₂ false
  ¬ : ∀ σ b t → (b , σ) ⇓₂ t → (¬ b , σ) ⇓₂ not t
  opb : ∀ σ b₁ b₂ t₁ t₂ → (b₁ , σ) ⇓₂ t₁ → (b₂ , σ) ⇓₂ t₂ → (opb b₁ b₂ , σ) ⇓₂ t₁
  opr : ∀ σ a₁ a₂ z₁ z₂ → (a₁ , σ) ⇓₁ z₁ → (a₂ , σ) ⇓₁ z₂ → (opr a₁ a₂ , σ) ⇓₂ true
  
record Eval (e : Set) (v : Set) : Set₁ where
  field _⇓_ : e × State → v → Set
  
evalAExp : Eval AExp ℕ
evalAExp = record { _⇓_ = _⇓₁_ }

evalBExp : Eval BExp Bool
evalBExp = record { _⇓_ = _⇓₂_ }

_⇓_ : {e v : Set} → {{eval : Eval e v}} → e × State → v → Set
_⇓_ {{eval}} = Eval._⇓_ eval

thm-AExp-det : ∀ {conf} → ∀ {z z' : ℕ} → conf ⇓ z
                                       → conf ⇓ z'
                                       → z ≡ z'
thm-AExp-det (var x σ) (var .x .σ) = refl
thm-AExp-det (num z' σ) (num .z' .σ) = refl
thm-AExp-det (op a₁ a₂ σ n m p₁ q₁) (op .a₁ .a₂ .σ n' m' p₂ q₂)
  with thm-AExp-det p₁ p₂ | thm-AExp-det q₁ q₂
thm-AExp-det (op a₁ a₂ σ n m _ _) (op .a₁ .a₂ .σ .n .m _ _) | refl | refl = refl

thm-BExp-det : ∀ {conf} → ∀ {z z' : Bool} → conf ⇓ z
                                          → conf ⇓ z'
                                          → z ≡ z'
thm-BExp-det (true σ) (true .σ) = refl
thm-BExp-det (false σ) (false .σ) = refl
thm-BExp-det (¬ σ b t p) (¬ .σ .b t₁ q)
  with thm-BExp-det p q
thm-BExp-det (¬ σ b t p) (¬ .σ .b .t q) | refl = refl
thm-BExp-det (opb σ b₁ b₂ z t p₁ q₁) (opb .σ .b₁ .b₂ z' t' p₂ q₂)
  with thm-BExp-det p₁ p₂ | thm-BExp-det q₁ q₂
thm-BExp-det (opb σ b₁ b₂ z t _ _) (opb .σ .b₁ .b₂ .z .t _ _) | refl | refl = refl
thm-BExp-det (opr σ a₁ a₂ z₁ z₂ p₁ q₁) (opr .σ .a₁ .a₂ z₃ z₄ p₂ q₂)
  with thm-AExp-det p₁ p₂ | thm-AExp-det q₁ q₂
thm-BExp-det (opr σ a₁ a₂ z z' _ _) (opr .σ .a₁ .a₂ .z .z' _  _) | refl | refl = refl

data ⟨_⟩→⟨_⟩ : Exp × State → Config → Set where
  skip   : ∀ σ → ⟨ skip , σ ⟩→⟨ inj₂ [] , σ ⟩
  ass    : ∀ σ v a z → (a , σ) ⇓ z → ⟨ ass v a , σ ⟩→⟨ inj₂ [] , (λ x → if x == v then z else (σ x)) ⟩
  comp₁  : ∀ σ σ' s₁ s₂ → ⟨ s₁ , σ ⟩→⟨ inj₂ [] , σ' ⟩ → ⟨ comp s₁ s₂ , σ ⟩→⟨ inj₁ s₂ , σ' ⟩
  comp₂  : ∀ σ σ' s₁ s₁' s₂ → ⟨ s₁ , σ ⟩→⟨ inj₁ s₁' , σ' ⟩ → ⟨ comp s₁ s₂ , σ ⟩→⟨ inj₁ (comp s₁' s₂) , σ' ⟩
  if₁    : ∀ σ s₁ s₂ b → (b , σ) ⇓ true → ⟨ if b then s₁ else s₂ fi , σ ⟩→⟨ inj₁ s₁ , σ ⟩
  if₂    : ∀ σ s₁ s₂ b → (b , σ) ⇓ false → ⟨ if b then s₁ else s₂ fi , σ ⟩→⟨ inj₁ s₂ , σ ⟩
  while₁ : ∀ σ s b → (b , σ) ⇓ true → ⟨ while b do s od , σ ⟩→⟨ inj₁ (comp s (while b do s od)) , σ ⟩
  while₂ : ∀ σ s b → (b , σ) ⇓ false → ⟨ while b do s od , σ ⟩→⟨ inj₂ [] , σ ⟩

thm-Exp-det : ∀ {S S' S'' σ σ' σ''} → ⟨ S , σ ⟩→⟨ S'  , σ'  ⟩
                                    → ⟨ S , σ ⟩→⟨ S'' , σ'' ⟩
                                    → (S' ≡ S'') × (σ' ≡ σ'')
thm-Exp-det (skip σ) (skip .σ) = refl , refl
thm-Exp-det (ass σ v a z x) (ass .σ .v .a z' x₁)
  with thm-AExp-det x x₁
thm-Exp-det (ass σ v a z x) (ass .σ .v .a .z x₁) | refl = refl , refl

thm-Exp-det (if₁ σ'' s₁ s₂ b _) (if₁ .σ'' .s₁ .s₂ .b _) = refl , refl
thm-Exp-det (if₁ σ'' s₁ s₂ b p) (if₂ .σ'' .s₁ .s₂ .b q)
  with thm-BExp-det p q
... | ()
thm-Exp-det (if₂ σ'' S'' S' b p) (if₁ .σ'' .S'' .S' .b q)
  with thm-BExp-det p q
... | ()
thm-Exp-det (if₂ σ'' s₁ S'' b _) (if₂ .σ'' .s₁ .S'' .b _) = refl , refl

thm-Exp-det (while₁ σ'' s b _ ) (while₁ .σ'' .s .b _) = refl , refl
thm-Exp-det (while₁ σ'' s b p) (while₂ .σ'' .s .b q)
  with thm-BExp-det p q
... | ()
thm-Exp-det (while₂ σ'' s b p) (while₁ .σ'' .s .b q)
  with thm-BExp-det p q
... | ()
thm-Exp-det (while₂ σ'' s b p) (while₂ .σ'' .s .b q) = refl , refl

thm-Exp-det (comp₁ σ σ' s₁ s₂ p) (comp₁ .σ σ'' .s₁ .s₂ q)
  with thm-Exp-det p q
thm-Exp-det (comp₁ σ σ' s₁ s₂ p) (comp₁ .σ .σ' .s₁ .s₂ q) | refl , refl = refl , refl

thm-Exp-det (comp₁ σ σ' s₁ s₂ p) (comp₂ .σ σ'' .s₁ s₁' .s₂ q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₂ σ σ' s₁ s₁' s₂ p) (comp₁ .σ σ'' .s₁ .s₂ q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₂ σ σ' s₁ s₁' s₂ p) (comp₂ .σ σ'' .s₁ s₁'' .s₂  q)
  with thm-Exp-det p q
thm-Exp-det (comp₂ σ σ' s₁ s₁' s₂ p) (comp₂ .σ .σ' .s₁ .s₁' .s₂ q) | refl , refl = refl , refl

data ⟨_⟩→_⟨_⟩ : Config → ℕ → Config → Set where
  stop : ∀ {σ} → ⟨ inj₂ [] , σ ⟩→ 0 ⟨ inj₂ [] , σ ⟩
  next : ∀ {n σ σ' σ'' s s'} → n > 0 → ⟨ s , σ ⟩→⟨ s' , σ' ⟩ → ⟨ s' , σ' ⟩→ (pred n) ⟨ inj₂ [] , σ'' ⟩ → ⟨ inj₁ s , σ ⟩→ n ⟨ inj₂ [] , σ'' ⟩

data _⟶_ : Config → State → Set where
  eval : ∀ {n c σ} → ⟨ c ⟩→ n ⟨ inj₂ [] , σ ⟩ → c ⟶ σ

--≤′-suc : ∀ {n m} → n ≤′ m → ℕ.suc n ≤′ ℕ.suc m
--≤′-suc ≤′-refl = ≤′-refl
--≤′-suc (≤′-step le) = ≤′-step (≤′-suc le)

≤-step : ∀ {m n} → m ≤ n → m ≤ ℕ.suc n
≤-step z≤n       = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

seq-decomp : ∀ {s₁ s₂ σ₁ σ₂} → ∀ n →  ⟨ inj₁ (comp s₁ s₂) , σ₁ ⟩→ n ⟨ inj₂ [] , σ₂ ⟩
                                      → ∃ \i → ∃ \j → ∃ \σ → ⟨ inj₁ s₁ , σ₁ ⟩→ i ⟨ inj₂ [] , σ ⟩
                                                             × ⟨ inj₁ s₂ , σ ⟩→ j ⟨ inj₂ [] , σ₂ ⟩
                                                             × i <′ n × j <′ n
seq-decomp ℕ.zero (next () step n-steps)
seq-decomp (ℕ.suc n) (next n>0 (comp₁ σ σ' s₁ s₂ step₁) (next n-1>0 step₂ n-1-steps))
           = 1 , n , σ' , next (s≤s z≤n) step₁ stop , (next n-1>0 step₂ n-1-steps) , s≤′s (≤⇒≤′ n-1>0) , ≤′-refl
seq-decomp (ℕ.suc n) (next {.(ℕ.suc n)} n>0 (comp₂ σ₁ σ' s₁ s₁' s₂ step) n-steps)
  with seq-decomp n n-steps
... | k , l , σ'' , k-steps , l-steps , k<n , l<n = ℕ.suc k ,
                                                      l ,
                                                      σ'' ,
                                                      next (s≤s z≤n) step k-steps , l-steps , s≤′s k<n , ≤′-step l<n
