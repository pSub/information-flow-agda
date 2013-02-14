open import Level
open import Data.Empty
open import Data.Bool
open import Data.Nat hiding(zero)
open import Data.Product
open import Data.Sum
open import Relation.Binary.Core
open import Function.Injection

open import Induction.Nat
open import Induction.WellFounded

open import Domain

module STS (Var : Set) (dom : Var → Dom) (_==_ : Var → Var → Bool) where

open import STWL Var  _==_ renaming (Exp to Stmt)

data Exp' : Set where
  aexp : AExp → Exp'
  bexp : BExp → Exp'

data ⊢_∶_ : Exp' → Dom → Set where
  num : ∀ {n} → ⊢ aexp (num n) ∶ low
  var : ∀ {x} → dom x ≡ low →  ⊢ aexp (var x) ∶ low
  opa : ∀ {a₁ a₂} → ⊢ (aexp a₁) ∶ low → ⊢ (aexp a₂) ∶ low → ⊢ aexp (opa a₁ a₂) ∶ low

  true  : ⊢ bexp true ∶ low
  false : ⊢ bexp false ∶ low
  ¬     : ∀ {b} → ⊢ (bexp b) ∶ low → ⊢ bexp (¬ b) ∶ low
  opb   : ∀ {b₁ b₂} → ⊢ (bexp b₁) ∶ low → ⊢ (bexp b₂) ∶ low → ⊢ bexp (opb b₁ b₂) ∶ low
  opr   : ∀ {a₁ a₂} → ⊢ (aexp a₁) ∶ low → ⊢ (aexp a₂) ∶ low → ⊢ bexp (opr a₁ a₂) ∶ low
  higha : ∀ {a} → ⊢ (aexp a) ∶ high
  highb : ∀ {b} → ⊢ (bexp b) ∶ high

⊬_∶_ : Exp' → Dom → Set
⊬ exp ∶ d = ⊢ exp ∶ d → ⊥

data [_]⊢_ : Dom → Stmt → Set where
  skip  : ∀ {pc} → [ pc ]⊢ skip
  sub   : ∀ {s} → [ high ]⊢ s → [ low ]⊢ s
  asgnh : ∀ {x pc exp} → dom x ≡ high → [ pc ]⊢ (ass x exp)
  asgnl : ∀ {x exp} → ⊢ (aexp exp) ∶ low → [ low ]⊢ (ass x exp)
  seq   : ∀ {s₁ s₂ pc} → [ pc ]⊢ s₁ → [ pc ]⊢ s₂ → [ pc ]⊢ (comp s₁ s₂)
  while : ∀ {b pc s} → ⊢ (bexp b) ∶ pc → [ pc ]⊢ s → [ pc ]⊢ (while b do s od)
  ite   : ∀ {b pc s₁ s₂} → ⊢ (bexp b) ∶ pc → [ pc ]⊢ s₁ → [ pc ]⊢ s₂ → [ pc ]⊢ if b then s₁ else s₂ fi

[_]⊬_ : Dom → Stmt → Set
[ pc ]⊬ s = [ pc ]⊢ s → ⊥

data _=L_ : Rel State zero where
  equal  : ∀ {σ σ'} → (∀ x → (dom x ≡ low) → (σ x ≡ σ' x)) → σ =L σ'

=L-refl : Reflexive _=L_
=L-refl = equal (λ x x-low → refl)

≡-trans : ∀ {a b c : ℕ} → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

=L-trans : Transitive _=L_
=L-trans (equal p) (equal q) = equal (λ x x-low → ≡-trans (p x x-low) (q x x-low))

≡-sym : ∀ {a b : ℕ} → a ≡ b → b ≡ a
≡-sym refl = refl

=L-sym : Symmetric _=L_
=L-sym (equal p) = equal (λ x x-low → ≡-sym (p x x-low))

data noninterferent_ : Stmt → Set where
  yes : ∀ {s} → (∀ σ₁ σ₁' σ₂ σ₂' → σ₁ =L σ₁'
                            → ( s , σ₁ ) ⟶ σ₂
                            → ( s , σ₁' ) ⟶ σ₂'
                            → σ₂ =L σ₂')
                            → noninterferent s
  
simple-security-aexp : ∀ {exp σ σ' v v'} → ⊢ (aexp exp) ∶ low
                                         → σ =L σ'
                                         → (exp , σ) ⇓₁ v
                                         → (exp , σ') ⇓₁ v'
                                         → v ≡ v'
simple-security-aexp num sim (num v σ) (num .v σ') = refl
simple-security-aexp (var x-low) (equal low-equal) (var x σ) (var .x σ') = low-equal x x-low
simple-security-aexp (opa type₁ type₂) l-equal (op a₁ a₂ σ n v a₁⇓ a₂⇓) (op .a₁ .a₂ σ' n₁ v' b₁⇓ b₂⇓)
  with simple-security-aexp type₁ l-equal a₁⇓ b₁⇓ | simple-security-aexp type₂ l-equal a₂⇓ b₂⇓
simple-security-aexp (opa p q) l (op a₁ a₂ σ n v a₁⇓ a₂⇓) (op .a₁ .a₂ σ' .n .v b₁⇓ b₂⇓) | refl | refl = refl


simple-security-bexp : ∀ {exp σ σ' v v'} → ⊢ (bexp exp) ∶ low
                                         → σ =L σ'
                                         → (exp , σ) ⇓₂ v
                                         → (exp , σ') ⇓₂ v'
                                         → v ≡ v'
simple-security-bexp true l-equal (true σ) (true σ') = refl
simple-security-bexp false l-equal (false σ) (false σ') = refl
simple-security-bexp (¬ type) l-equal (¬ σ b t b⇓) (¬ σ' .b t₁ c⇓)
  with simple-security-bexp type l-equal b⇓ c⇓
simple-security-bexp (¬ type) sim (¬ σ b t b⇓) (¬ σ' .b .t c⇓) | refl = refl
simple-security-bexp (opb type₁ type₂) sim (opb σ b₁ b₂ v t e₁ e₂) (opb σ' .b₁ .b₂ v' t' f₁ f₂)
  with simple-security-bexp type₁ sim e₁ f₁ | simple-security-bexp type₂ sim e₂ f₂
simple-security-bexp (opb type₁ type₂) sim (opb σ b₁ b₂ v t e₁ e₂) (opb σ' .b₁ .b₂ .v .t f₁ f₂) | refl | refl = refl
simple-security-bexp (opr type₁ type₂) sim (opr σ a₁ a₂ z₁ z₂ e₁ e₂) (opr σ' .a₁ .a₂ z₁' z₂' f₁ f₂)
  with simple-security-aexp type₁ sim e₁ f₁ | simple-security-aexp type₂ sim e₂ f₂
simple-security-bexp (opr type₁ type₂) sim (opr σ a₁ a₂ z₁ z₂ e₁ e₂) (opr σ' .a₁ .a₂ .z₁ .z₂ f₁ f₂) | refl | refl = refl

-- TODO: Proof these lemmata
postulate
  lemma : ∀ {A : Set} {x y} {a b : A} → dom(x) ≡ low → dom(y) ≡ high → a ≡ (if x == y then b else a)
  
postulate
  lemma2 : ∀ {A : Set} {x y} {a b c d : A} → dom(x) ≡ low → dom(y) ≡ high → c ≡ d → (if x == y then a else c) ≡ (if x == y then b else d)

confinment : ∀ {s₁ s₂ σ₁ σ₂} → [ high ]⊢ s₁
                             → ⟨ s₁ , σ₁ ⟩→⟨ s₂ , σ₂ ⟩
                             → σ₁ =L σ₂
confinment skip (skip σ₂) = =L-refl
confinment (asgnh x-high) (ass σ₁ x exp z x₂) = equal (λ y y-low → lemma y-low x-high)
confinment (seq type₁ type₂) (comp₁ σ₁ σ₂ s₁ s₂ s₂≠[] exec)
  with confinment type₁ exec
... | equal x = equal x
confinment (seq type₁ type₂) (comp₂ σ₁ σ₂ s₁ s₁' s₂ s₁≠[] exec)
  with confinment type₁ exec
... | equal x = equal x
confinment (while b-high type) (while₁ σ₂ s b b-true) = equal (λ x x-low → refl)
confinment (while b-high type) (while₂ σ₂ s b b-false) = equal (λ x x-low → refl)
confinment (ite x type₁ type₂) (if₁ σ₂ s₁ s₂ b _ _ x₁) = equal (λ x x-low → refl)
confinment (ite x type₁ type₂) (if₂ σ₂ s₁ s₂ b _ _ x₁) = equal (λ x x-low → refl)


high-typed-stmts : ∀ {s₁ s₂ σ₁ σ₂} → [ high ]⊢ s₁ → ⟨ s₁ , σ₁ ⟩→⟨ s₂ , σ₂ ⟩
                                   → ( s₂ ≡ [] ⊎ [ high ]⊢ s₂ )
high-typed-stmts {.skip} {.[]} skip (skip σ₂) = inj₁ refl
high-typed-stmts {(ass x exp)} {.[]} (asgnh x-high) (ass σ₁ .x .exp z x₂) = inj₁ refl
high-typed-stmts (seq s₁-high s₂-high) (comp₁ σ₁ σ₂ s₁ s₂ s₁-s₂ s₂≠[]) = inj₂ s₂-high
high-typed-stmts (seq s₁-high s₂-high) (comp₂ σ₁ σ₂ s₁ s₁' s₂ s₁'-ne-[] s₁-s₁')
  with high-typed-stmts s₁-high s₁-s₁'
high-typed-stmts (seq s₁-high s₂-high) (comp₂ σ₁ σ₂ s₁ .[] s₂ s₁'-ne-[] s₁-s₁') | inj₁ refl
  with s₁'-ne-[] refl
... | ()
high-typed-stmts (seq s₁-high s₂-high) (comp₂ σ₁ σ₂ s₁ s₁' s₂ s₁'-ne-[] s₁-s₁') | inj₂ s₁'-high = inj₂ (seq s₁'-high s₂-high)
high-typed-stmts (while b-high s-high) (while₁ σ₂ s b x₁) = inj₂ (seq s-high (while b-high s-high))
high-typed-stmts {(while b do s od)} {.[]} (while b-high s₁-high) (while₂ σ₂ .s .b x₁) = inj₁ refl
high-typed-stmts (ite b-high s₁-high s₂-high) (if₁ σ₂ s₁ s₂ b _ _ x₁) = inj₂ s₁-high
high-typed-stmts (ite b-high s₁-high s₂-high) (if₂ σ₂ s₁ s₂ b _ _ x₁) = inj₂ s₂-high


confined-sequence : ∀ {n s σ σ'} → [ high ]⊢ s → ⟨ s , σ ⟩→ n ⟨ [] , σ' ⟩ → σ =L σ'
confined-sequence {ℕ.zero} () stop
confined-sequence {ℕ.zero} s-high (next () step n-steps)
confined-sequence {ℕ.suc n} s-high (next n>0 step step-n)
  with confinment s-high step | high-typed-stmts s-high step
confined-sequence {ℕ.suc .0} s-high (next n>0 step stop) | σ=Lσ'' | inj₁ refl = σ=Lσ''
confined-sequence {ℕ.suc n} s-high (next n>0 step (next n>0' () step-n)) | σ=Lσ'' | inj₁ refl
confined-sequence {ℕ.suc n} s-high (next n>0 step step-n) | σ=Lσ'' | inj₂ s'-high
  with confined-sequence s'-high step-n
... | σ''=Lσ' = =L-trans σ=Lσ'' σ''=Lσ'

if-low-equal : ∀ {x σ σ' z z'} → (b : Bool) → σ =L σ' → z ≡ z' → dom(x) ≡ low → (if b then z else σ x) ≡ (if b then z' else σ' x)
if-low-equal true l-equal z=z' x-low = z=z'
if-low-equal {x} false (equal f) z=z' x-low = f x x-low

soundness' : ∀ {n m pc s σ₁ σ₁' σ₂ σ₂'} → Acc _<′_ n
                                        → Acc _<′_ m
                                        → [ pc ]⊢ s
                                        → ⟨ s , σ₁ ⟩→ n ⟨ [] , σ₂ ⟩
                                        → ⟨ s , σ₁' ⟩→ m ⟨ [] , σ₂' ⟩
                                        → σ₁ =L σ₁'
                                        → σ₂ =L σ₂'
soundness' {ℕ.zero} {ℕ.zero} _ _ _ stop stop l-equal = l-equal
soundness' {ℕ.zero} {ℕ.zero} _ _ _ stop (next () step m-steps) l-equal
soundness' {ℕ.zero} {ℕ.zero} _ _ _ (next () step n-steps) stop l-equal
soundness' {ℕ.zero} {ℕ.zero} _ _ _ (next () step n-steps) (next () step' m-steps) l-equal
soundness' {ℕ.zero} {ℕ.suc m} _ _ _ stop (next n>0 () m-steps) l-equal
soundness' {ℕ.zero} {ℕ.suc m} _ _ _ (next () step n-steps) m-steps l-equal
soundness' {ℕ.suc n} {ℕ.zero} _ _ _ (next n>0 () n-steps) stop l-equal
soundness' {ℕ.suc n} {ℕ.zero} _ _ _ n-steps (next () m-step m-steps) l-equal

soundness' {ℕ.suc n} {ℕ.suc m} {low} {[]} _ _ _ (next n>0 () n-steps) m-steps l-equal

soundness' {ℕ.suc .0} {ℕ.suc .0} {low} _ _ _ (next n>0 (skip σ₂) stop) (next n>0' (skip σ₂') stop) l-equal = l-equal
soundness' {ℕ.suc .0} {ℕ.suc m} {low} _ _ _ (next n>0 (skip σ₂) stop) (next n>0' (skip σ'') (next n>0'' () m-steps)) l-equal 
soundness' {ℕ.suc n} {ℕ.suc m} {low} _ _ _ (next n>0 (skip σ) (next n>0' () n-steps)) m-steps l-equal

soundness' {ℕ.suc .0} {ℕ.suc .0} {low} _ _ (asgnh x-high) (next x₁ (ass σ₁ x exp z x') stop) (next x₄ (ass σ₁' .x .exp z₁ x₅) stop) (equal σ₁=σ₁') = equal (λ y y-low → lemma2 y-low x-high (σ₁=σ₁' y y-low))
soundness' {ℕ.suc .0} {ℕ.suc m} {low} _ _ (asgnh x₂) (next x₁ (ass σ₁ x exp z x-high) stop) (next x₄ (ass σ₁' .x .exp z₁ x₅) (next x₃ () m-steps)) l-equal
soundness' {ℕ.suc n} {ℕ.suc m} {low} _ _ (asgnh x₂) (next x₁ (ass σ₁ x exp z x-high) (next x₃ () n-steps)) (next x₅ (ass σ₁' .x .exp z₁ x₆) m-steps) l-equal

soundness' {ℕ.suc .0} {ℕ.suc .0} {low} _ _ (asgnl x-low) (next x₁ (ass σ₁ x exp z x₃) stop) (next x₄ (ass σ₁' .x .exp z₁ x₅) stop) l-equal
  with simple-security-aexp x-low l-equal x₃ x₅
... | z=z' = equal (λ y y-low → if-low-equal (y == x) l-equal z=z' y-low)
soundness' {ℕ.suc .0} {ℕ.suc m} {low} _ _ (asgnl x-low) (next x₁ (ass σ₁ x exp z x₃) stop) (next x₄ (ass σ₁' .x .exp z₁ x₅) (next x₂ () m-steps)) l-equal
soundness' {ℕ.suc n} {ℕ.suc m} {low} _ _ (asgnl x-low) (next x₁ (ass σ₁ x exp z x₃) (next x₂ () n-steps)) (next x₅ (ass σ₁' .x .exp z₁ x₆) m-steps) l-equal

soundness' {ℕ.suc n} {ℕ.suc m} {low} (acc f) (acc g) (seq typeable₁ typeable₂) n-steps m-steps l-equal
  with seq-decomp n-steps | seq-decomp m-steps
... | k , l , _ , s₁ , s₂ , k<n , l<n | i , h , _ , s₁' , s₂' , i<n , h<n
  with soundness' (f k k<n) (g i i<n) typeable₁ s₁ s₁' l-equal
... | σ=Lσ'
  with soundness' (f l l<n) (g h h<n) typeable₂ s₂ s₂' σ=Lσ'
... | σ₂=Lσ₂' = σ₂=Lσ₂'

soundness' {ℕ.suc n} {ℕ.suc m} {low} (acc f) (acc g) (ite b-high t₁ t₂) (next n>0 (if₁ σ' s' s₂ b _ _ x₁) n-steps) (next m>0 (if₁ σ'' .s' .s₂ .b _ _ x₂) m-steps) l-equal
  with soundness' (f n ≤′-refl) (g m ≤′-refl) t₁ n-steps m-steps l-equal
... | σ₂=Lσ₂' = σ₂=Lσ₂'
soundness' {ℕ.suc n} {ℕ.suc m} {low} _ _ (ite b-low t₁ t₂) (next n>0 (if₁ σ' s' s'' b _ _ x₁) n-steps) (next m>0 (if₂ σ'' .s' .s'' .b _ _ x₂) m-steps) l-equal
  with simple-security-bexp b-low l-equal x₁ x₂
... | ()
soundness' {ℕ.suc n} {ℕ.suc m} {low} _ _ (ite b-low t₁ t₂) (next n>0 (if₂ σ' s'' s' b _ _ x₁) n-steps) (next m>0 (if₁ σ'' .s'' .s' .b _ _ x₂) m-steps) l-equal
  with simple-security-bexp b-low l-equal x₁ x₂
... | ()
soundness' {ℕ.suc n} {ℕ.suc m} {low} (acc f) (acc g) (ite b-low t₁ t₂) (next n>0 (if₂ σ' s₁ s' b _ _ x₁) n-steps) (next m>0 (if₂ σ'' .s₁ .s' .b _ _ x₂) m-steps) l-equal
  with soundness' (f n ≤′-refl) (g m ≤′-refl) t₂ n-steps m-steps l-equal
... | σ₂=Lσ₂' = σ₂=Lσ₂'

soundness' {ℕ.suc n} {ℕ.suc m} {low} (acc f) (acc g) (while b-low t) (next n>0 (while₁ σ s b b-true) n-steps) (next x₃ (while₁ σ' .s .b b-true') m-steps) l-equal
  with soundness' (f n ≤′-refl) (g m ≤′-refl) (seq t (while b-low t)) n-steps m-steps l-equal
... | σ₂=Lσ₂' = σ₂=Lσ₂'
soundness' {ℕ.suc n} {ℕ.suc m} {low} _ _ (while b-low t) (next n>0 (while₁ σ' s b x₂) n-steps) (next x₃ (while₂ σ'' .s .b x₄) m-steps) l-equal
  with simple-security-bexp b-low l-equal x₂ x₄
... | ()
soundness' {ℕ.suc n} {ℕ.suc m} {low} _ _ (while b-low t) (next n>0 (while₂ σ' s b x₂) n-steps) (next x₃ (while₁ σ'' .s .b x) m-steps) l-equal
  with simple-security-bexp b-low l-equal x₂ x
... | ()
soundness' {ℕ.suc .0} {ℕ.suc .0} {low} _ _ (while b-low t) (next n>0 (while₂ σ₂ s b x₂) stop) (next x₃ (while₂ σ₂' .s .b x) stop) l-equal = l-equal
soundness' {ℕ.suc .0} {ℕ.suc m} {low} _ _ (while b-low t) (next n>0 (while₂ σ₂ s b x₂) stop) (next  x₃ (while₂ σ' .s .b x) (next x₄ () m-steps)) l-equal
soundness' {ℕ.suc n} {ℕ.suc .0} {low} _ _ (while b-low t) (next n>0 (while₂ σ s b x₂) (next x () n-steps)) (next x₄ (while₂ σ' .s .b x₅) stop) l-equal
soundness' {ℕ.suc n} {ℕ.suc m} {low} _ _ (while b-low t) (next n>0 (while₂ σ s b x₂) (next x x₃ n-steps)) (next x₄ (while₂ σ' .s .b x₅) (next x₆ () m-steps)) l-equal

soundness' {ℕ.suc n} {ℕ.suc m} {high} _ _ typeable n-steps m-steps l-equal
  with confined-sequence typeable n-steps | confined-sequence typeable m-steps
... | σ₁=Lσ₂ | σ₁'=Lσ₂' = =L-trans (=L-trans (=L-sym σ₁=Lσ₂) l-equal) σ₁'=Lσ₂'
soundness' {ℕ.suc n} {ℕ.suc m} {low} _ _ (sub typeable) n-steps m-steps l-equal
  with confined-sequence typeable n-steps | confined-sequence typeable m-steps
... | σ₁=Lσ₂ | σ₁'=Lσ₂' = =L-trans (=L-trans (=L-sym σ₁=Lσ₂) l-equal) σ₁'=Lσ₂'

soundness : ∀ {pc s} → [ pc ]⊢ s → noninterferent s
soundness typeable = yes (λ {σ₁ σ₁' σ₂ σ₂' l-equal (eval {n} n-steps) (eval {m} m-steps)
                          → soundness' (<-well-founded n) (<-well-founded m) typeable n-steps m-steps l-equal})
