open import Level
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
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

-- TODO: remove [] from Exp
data Exp : Set where
  [] : Exp
  skip : Exp
  ass : Var → AExp → Exp
  comp : Exp → Exp → Exp
  if_then_else_fi : BExp → Exp → Exp → Exp
  while_do_od : BExp → Exp → Exp

State = Var → ℕ
Config = Exp × State

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

data ⟨_⟩→⟨_⟩ : Config → Config → Set where
  skip   : ∀ σ → ⟨ skip , σ ⟩→⟨ [] , σ ⟩
  ass    : ∀ σ v a z → (a , σ) ⇓ z → ⟨ ass v a , σ ⟩→⟨ [] , (λ x → if x == v then z else (σ x)) ⟩
  comp₁  : ∀ σ σ' s₁ s₂ → s₂ ≢ [] → ⟨ s₁ , σ ⟩→⟨ [] , σ' ⟩ → ⟨ comp s₁ s₂ , σ ⟩→⟨ s₂ , σ' ⟩
  comp₂  : ∀ σ σ' s₁ s₁' s₂ → s₁' ≢ [] → ⟨ s₁ , σ ⟩→⟨ s₁' , σ' ⟩ → ⟨ comp s₁ s₂ , σ ⟩→⟨ comp s₁' s₂ , σ' ⟩
  if₁    : ∀ σ s₁ s₂ b → s₁ ≢ [] → s₂ ≢ [] → (b , σ) ⇓ true → ⟨ if b then s₁ else s₂ fi , σ ⟩→⟨ s₁ , σ ⟩
  if₂    : ∀ σ s₁ s₂ b → s₁ ≢ [] → s₂ ≢ [] → (b , σ) ⇓ false → ⟨ if b then s₁ else s₂ fi , σ ⟩→⟨ s₂ , σ ⟩
  while₁ : ∀ σ s b → (b , σ) ⇓ true → ⟨ while b do s od , σ ⟩→⟨ comp s (while b do s od) , σ ⟩
  while₂ : ∀ σ s b → (b , σ) ⇓ false → ⟨ while b do s od , σ ⟩→⟨ [] , σ ⟩

thm-Exp-det : ∀ {S S' S'' σ σ' σ''} → ⟨ S , σ ⟩→⟨ S'  , σ'  ⟩
                                    → ⟨ S , σ ⟩→⟨ S'' , σ'' ⟩
                                    → (S' ≡ S'') × (σ' ≡ σ'')
thm-Exp-det (skip σ'') (skip .σ'') = refl , refl
thm-Exp-det (ass σ'' v a z x) (ass .σ'' .v .a z' x₁)
  with thm-AExp-det x x₁
thm-Exp-det (ass σ'' v a z x) (ass .σ'' .v .a .z x₁) | refl = refl , refl

thm-Exp-det (comp₁ σ σ' s₁ s₂ s₂≠[] p) (comp₁ .σ σ'' .s₁ .s₂ s₂≠[]' q)
  with thm-Exp-det p q
thm-Exp-det (comp₁ σ σ' s₁ s₂ s₂≠[] p) (comp₁ .σ .σ' .s₁ .s₂ s₂≠[]' q) | refl , refl = refl , refl

thm-Exp-det (comp₁ σ σ' s₁ s₂ s₂≠[] p) (comp₂ .σ σ'' .s₁ [] .s₂ ne[] q)
  with ne[] refl
... | ()
thm-Exp-det (comp₁ σ σ' s₁ s₂ s₂≠[] p) (comp₂ .σ σ'' .s₁ skip .s₂ ne[] q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₁ σ σ' s₁ s₂ s₂≠[] p) (comp₂ .σ σ'' .s₁ (ass x x₁) .s₂ ne[] q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₁ σ σ' s₁ s₂ s₂≠[] p) (comp₂ .σ σ'' .s₁ (comp s₁' s₁'') .s₂ ne[] q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₁ σ σ' s₁ s₂ s₂≠[] p) (comp₂ .σ σ'' .s₁ if x then s₁' else s₁'' fi .s₂ ne[] q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₁ σ σ' s₁ s₂ s₂≠[] p) (comp₂ .σ σ'' .s₁ while x do s₁' od .s₂ ne[] q)
  with thm-Exp-det p q
... | () , _


thm-Exp-det (comp₂ σ σ' s₁ [] s₂ ne[] p) (comp₁ .σ σ'' .s₁ .s₂ s₂≠[] q)
  with ne[] refl
... | ()
thm-Exp-det (comp₂ σ σ' s₁ skip s₂ ne[] p) (comp₁ .σ σ'' .s₁ .s₂ s₂≠[] q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₂ σ σ' s₁ (ass x x₁) s₂ ne[] p) (comp₁ .σ σ'' .s₁ .s₂ s₂≠[] q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₂ σ σ' s₁ (comp s₁' s₁'') s₂ ne[] p) (comp₁ .σ σ'' .s₁ .s₂ s₂≠[] q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₂ σ σ' s₁ if x then s₁' else s₁'' fi s₂ ne[] p) (comp₁ .σ σ'' .s₁ .s₂ s₂≠[] q)
  with thm-Exp-det p q
... | () , _
thm-Exp-det (comp₂ σ σ' s₁ while x do s₁' od s₂ ne[] p) (comp₁ .σ σ'' .s₁ .s₂ s₂≠[] q)
  with thm-Exp-det p q
... | () , _

thm-Exp-det (comp₂ σ σ' s₁ s₁' s₂ ne[] p) (comp₂ .σ σ'' .s₁ s₁'' .s₂ ne[]' q)
  with thm-Exp-det p q
thm-Exp-det (comp₂ σ σ' s₁ s₁' s₂ ne[] p) (comp₂ .σ .σ' .s₁ .s₁' .s₂ ne[]' q) | refl , refl = refl , refl

thm-Exp-det (if₁ σ'' s₁ s₂ b _ _ _) (if₁ .σ'' .s₁ .s₂ .b _ _ _) = refl , refl
thm-Exp-det (if₁ σ'' s₁ s₂ b _ _ p) (if₂ .σ'' .s₁ .s₂ .b _ _ q)
  with thm-BExp-det p q
... | ()
thm-Exp-det (if₂ σ'' S'' S' b _ _ p) (if₁ .σ'' .S'' .S' .b _ _ q)
  with thm-BExp-det p q
... | ()
thm-Exp-det (if₂ σ'' s₁ S'' b _ _ _) (if₂ .σ'' .s₁ .S'' .b _ _ _) = refl , refl

thm-Exp-det (while₁ σ'' s b _ ) (while₁ .σ'' .s .b _) = refl , refl
thm-Exp-det (while₁ σ'' s b p) (while₂ .σ'' .s .b q)
  with thm-BExp-det p q
... | ()
thm-Exp-det (while₂ σ'' s b p) (while₁ .σ'' .s .b q)
  with thm-BExp-det p q
... | ()
thm-Exp-det (while₂ σ'' s b p) (while₂ .σ'' .s .b q) = refl , refl

data ⟨_⟩→_⟨_⟩ : Config → ℕ → Config → Set where
  stop : ∀ {σ} → ⟨ [] , σ ⟩→ 0 ⟨ [] , σ ⟩
  next : ∀ {n σ σ' σ'' s s'} → n > 0 → ⟨ s , σ ⟩→⟨ s' , σ' ⟩ → ⟨ s' , σ' ⟩→ (pred n) ⟨ [] , σ'' ⟩ → ⟨ s , σ ⟩→ n ⟨ [] , σ'' ⟩

data _⟶_ : Config → State → Set where
  eval : ∀ {n c σ} → ⟨ c ⟩→ n ⟨ [] , σ ⟩ → c ⟶ σ

≤′-suc : ∀ {n m} → n ≤′ m → ℕ.suc n ≤′ ℕ.suc m
≤′-suc ≤′-refl = ≤′-refl
≤′-suc (≤′-step le) = ≤′-step (≤′-suc le)

seq-decomp : ∀ {n s₁ s₂ σ₁ σ₂} →  ⟨ comp s₁ s₂ , σ₁ ⟩→ n ⟨ [] , σ₂ ⟩
                               → ∃ \i → ∃ \j → ∃ \σ → ⟨ s₁ , σ₁ ⟩→ i ⟨ [] , σ ⟩
                                                     × ⟨ s₂ , σ ⟩→ j ⟨ [] , σ₂ ⟩
                                                     × i <′ n × j <′ n
seq-decomp {ℕ.zero} (next () step n-steps)
seq-decomp {ℕ.suc n} {[]} (next x (comp₁ σ σ' .[] s' s₂≠[] ()) n-steps)
seq-decomp {ℕ.suc n} {[]} (next x (comp₂ σ σ' .[] s₁' s₂ s₁'≠[] ()) n-steps)
seq-decomp {ℕ.suc .0} {skip} {.[]} (next _ (comp₁ σ σ' .skip .[] s₂≠[] step) stop)
  with s₂≠[] refl
... | ()
seq-decomp {ℕ.suc n} {skip} (next _ (comp₁ σ σ' .skip s' s₂≠[] step) (next n>0 step' n-steps))
           = 1 , (n , (σ' , (next (s≤s z≤n) step stop) , (next n>0 step' n-steps) , ≤′-suc (≤⇒≤′ n>0) , ≤′-refl))
seq-decomp {ℕ.suc n} {skip} (next _ (comp₂ σ' .σ' .skip .[] s₂ s₁'≠[] (skip .σ')) n-steps)
  with s₁'≠[] refl
... | ()
seq-decomp {ℕ.suc .0} {ass x a} {.[]} (next _ (comp₁ σ σ' .(ass x a) .[] s₂≠[] step) stop)
  with s₂≠[] refl
... | ()
seq-decomp {ℕ.suc n} {ass x a} (next _ (comp₁ σ σ' .(ass x a) s' s₂≠[] step) (next n>0 step' n-steps))
           = 1 , (n , (σ' , (next (s≤s z≤n) step stop) , (next n>0 step' n-steps) , ≤′-suc (≤⇒≤′ n>0) , ≤′-refl))
seq-decomp {ℕ.suc n} {ass x a} (next _ (comp₂ σ' .(λ x₁ → if x₁ == x then z else σ' x₁) .(ass x a) .[] s₂ s₁'≠[] (ass .σ' .x .a z x₂)) n-steps)
  with s₁'≠[] refl
... | ()

seq-decomp {ℕ.suc .0} {comp s₁ s₂} {.[]} (next _ (comp₁ σ σ' .(comp s₁ s₂) .[] ≠[] step) stop)
  with ≠[] refl
... | ()
seq-decomp {ℕ.suc n} {comp s₁ .[]} (next _ (comp₁ σ σ' .(comp s₁ []) s₂ _ (comp₁ .σ .σ' .s₁ .[] ≠[] step)) n-steps)
  with ≠[] refl
... | ()
seq-decomp {ℕ.suc n} {comp s₁ s₂} (next n>0 (comp₂ σ σ' .(comp s₁ s₂) s₁' s₃ ≠[] step) n-steps)
  with seq-decomp n-steps
... | k , l , σ'' , k-steps , l-steps , k<n , l<n
    = (ℕ.suc k) , (l , (σ'' , ((next (s≤s z≤n) step k-steps) , l-steps , ((s≤′s k<n) , ≤′-step l<n))))

seq-decomp {ℕ.suc .0} {if x then s₁ else s₂ fi} {.[]} (next n>0 (comp₁ σ σ' .(if x then s₁ else s₂ fi) .[] ≠[] step) stop)
  with ≠[] refl
... | ()
seq-decomp {ℕ.suc n} {if x then .[] else s₂ fi} (next n>0 (comp₁ σ .σ .(if x then [] else s₂ fi) s' x₂ (if₁ .σ .[] .s₂ .x s₁≠[] _ x₃)) n-steps)
  with s₁≠[] refl
... | ()
seq-decomp {ℕ.suc n} {if x then s₁ else .[] fi} (next n>0 (comp₁ σ .σ .(if x then s₁ else [] fi) s' x₂ (if₂ .σ .s₁ .[] .x _ s₂≠[] x₃)) n-steps)
  with s₂≠[] refl
... | ()
seq-decomp {ℕ.suc n} {if x then s₁ else s₂ fi} (next x₁ (comp₂ σ .σ .(if x then s₁ else s₂ fi) .s₁ s₃ x₂ (if₁ .σ .s₁ .s₂ .x x₃ x₄ x₅)) n-steps)
  with seq-decomp n-steps
... | k , l , σ' , k-steps , l-steps , k<n , l<n
    = (ℕ.suc k) , (l , (σ' , (next (s≤s z≤n) (if₁ σ s₁ s₂ x x₃ x₄ x₅) k-steps , l-steps , ((s≤′s k<n) , ≤′-step l<n))))
seq-decomp {ℕ.suc n} {if x then s₁ else .s₁' fi} (next x₁ (comp₂ .σ' σ' .(if x then s₁ else s₁' fi) s₁' s₃ x₂ (if₂ .σ' .s₁ .s₁' .x x₃ x₄ x₅)) n-steps)
  with seq-decomp n-steps
... | k , l , σ , k-steps , l-steps , k<n , l<n
    = (ℕ.suc k) , (l , (σ , (next (s≤s z≤n) (if₂ σ' s₁ s₁' x x₃ x₄ x₅) k-steps , l-steps , ((s≤′s k<n) , ≤′-step l<n))))

seq-decomp {ℕ.suc .0} {while x do s₁ od} {.[]} (next x₁ (comp₁ σ₂ .σ₂ .(while x do s₁ od) .[] ≠[] (while₂ .σ₂ .s₁ .x x₄)) stop)
  with ≠[] refl
... | ()
seq-decomp {ℕ.suc n} {while x do s₁ od} (next x₁ (comp₁ .σ' σ' .(while x do s₁ od) s' x₂ (while₂ .σ' .s₁ .x x₄)) (next n>0 step n-steps))
           = 1 , (n , (σ' , ((next (s≤s z≤n) (while₂ σ' s₁ x x₄) stop) , (next n>0 step n-steps) , (≤′-suc (≤⇒≤′ n>0) , ≤′-refl))))
seq-decomp {ℕ.suc n} {while x do s₁ od} (next x₁ (comp₂ σ₁ σ' .(while x do s₁ od) s₁' s₂ x₂ step) n-steps)
  with seq-decomp n-steps
... | k , l , σ , k-steps , l-steps , k<n , l<n
    = (ℕ.suc k) , (l , (σ , ((next (s≤s z≤n) step k-steps) , l-steps , ((s≤′s k<n) , (≤′-step l<n)))))

