open import Level
open import Data.Empty
open import Data.Bool
open import Data.Nat hiding(zero)
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Relation.Binary.Core
open import Function.Injection

open import Induction.Nat
open import Induction.WellFounded

open import SecurityDomain

module SecurityTypeSystem (Var : Set) (dom : Var → Dom) (_==_ : Var → Var → Bool) where

open import OperationalSemantics Var  _==_ renaming (Exp to Stmt)

data Exp' : Set where
  aexp : AExp → Exp'
  bexp : BExp → Exp'

data ⊢_∶_ : Exp' → Dom → Set where
  num : ∀ {n} → ⊢ aexp (num n) ∶ low
  var : ∀ {x} → dom x ≡ low →  ⊢ aexp (var x) ∶ low
  opₐ : ∀ {a₁ a₂} → ⊢ (aexp a₁) ∶ low → ⊢ (aexp a₂) ∶ low → ⊢ aexp (opₐ a₁ a₂) ∶ low

  true  : ⊢ bexp true ∶ low
  false : ⊢ bexp false ∶ low
  ¬     : ∀ {b} → ⊢ (bexp b) ∶ low → ⊢ bexp (¬ b) ∶ low
  opₚ   : ∀ {b₁ b₂} → ⊢ (bexp b₁) ∶ low → ⊢ (bexp b₂) ∶ low → ⊢ bexp (opₚ b₁ b₂) ∶ low
  opᵣ   : ∀ {a₁ a₂} → ⊢ (aexp a₁) ∶ low → ⊢ (aexp a₂) ∶ low → ⊢ bexp (opᵣ a₁ a₂) ∶ low
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

data _=ₗ_ : Rel State zero where
  equal  : ∀ {σ σ'} → (∀ x → (dom x ≡ low) → (σ x ≡ σ' x)) → σ =ₗ σ'

=ₗ-refl : Reflexive _=ₗ_
=ₗ-refl = equal (λ x x-low → refl)

≡-trans : ∀ {a b c : ℕ} → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

=ₗ-trans : Transitive _=ₗ_
=ₗ-trans (equal p) (equal q) = equal (λ x x-low → ≡-trans (p x x-low) (q x x-low))

≡-sym : ∀ {a b : ℕ} → a ≡ b → b ≡ a
≡-sym refl = refl

=ₗ-sym : Symmetric _=ₗ_
=ₗ-sym (equal p) = equal (λ x x-low → ≡-sym (p x x-low))

data noninterferent_ : Stmt → Set where
  yes : ∀ {s} → (∀ σ₁ σ₁' σ₂ σ₂' → σ₁ =ₗ σ₁'
                            → ( inj₁ s , σ₁ ) ⟶ σ₂
                            → ( inj₁ s , σ₁' ) ⟶ σ₂'
                            → σ₂ =ₗ σ₂')
                            → noninterferent s
  
simple-security-aexp : ∀ {exp σ σ' v v'} → ⊢ (aexp exp) ∶ low
                                         → σ =ₗ σ'
                                         → (exp , σ) ⇓ v
                                         → (exp , σ') ⇓ v'
                                         → v ≡ v'
simple-security-aexp num sim (num v σ) (num .v σ') = refl
simple-security-aexp (var x-low) (equal low-equal) (var x σ) (var .x σ') = low-equal x x-low
simple-security-aexp (opₐ type₁ type₂) l-equal (op a₁ a₂ σ n v a₁⇓ a₂⇓) (op .a₁ .a₂ σ' n₁ v' b₁⇓ b₂⇓)
  with simple-security-aexp type₁ l-equal a₁⇓ b₁⇓ | simple-security-aexp type₂ l-equal a₂⇓ b₂⇓
simple-security-aexp (opₐ p q) l (op a₁ a₂ σ n v a₁⇓ a₂⇓) (op .a₁ .a₂ σ' .n .v b₁⇓ b₂⇓) | refl | refl = refl


simple-security-bexp : ∀ {exp σ σ' v v'} → ⊢ (bexp exp) ∶ low
                                         → σ =ₗ σ'
                                         → (exp , σ) ⇓ v
                                         → (exp , σ') ⇓ v'
                                         → v ≡ v'
simple-security-bexp true l-equal (true σ) (true σ') = refl
simple-security-bexp false l-equal (false σ) (false σ') = refl
simple-security-bexp (¬ type) l-equal (¬ σ b t b⇓) (¬ σ' .b t₁ c⇓)
  with simple-security-bexp type l-equal b⇓ c⇓
simple-security-bexp (¬ type) sim (¬ σ b t b⇓) (¬ σ' .b .t c⇓) | refl = refl
simple-security-bexp (opₚ type₁ type₂) sim (opₚ σ b₁ b₂ v t e₁ e₂) (opₚ σ' .b₁ .b₂ v' t' f₁ f₂)
  with simple-security-bexp type₁ sim e₁ f₁ | simple-security-bexp type₂ sim e₂ f₂
simple-security-bexp (opₚ type₁ type₂) sim (opₚ σ b₁ b₂ v t e₁ e₂) (opₚ σ' .b₁ .b₂ .v .t f₁ f₂) | refl | refl = refl
simple-security-bexp (opᵣ type₁ type₂) sim (opᵣ σ a₁ a₂ z₁ z₂ e₁ e₂) (opᵣ σ' .a₁ .a₂ z₁' z₂' f₁ f₂)
  with simple-security-aexp type₁ sim e₁ f₁ | simple-security-aexp type₂ sim e₂ f₂
simple-security-bexp (opᵣ type₁ type₂) sim (opᵣ σ a₁ a₂ z₁ z₂ e₁ e₂) (opᵣ σ' .a₁ .a₂ .z₁ .z₂ f₁ f₂) | refl | refl = refl

-- TODO: Proof these lemmata
postulate
  lemma : ∀ {A : Set} {x y} {a b : A} → dom(x) ≡ low → dom(y) ≡ high → a ≡ (if x == y then b else a)
  
postulate
  lemma2 : ∀ {A : Set} {x y} {a b c d : A} → dom(x) ≡ low → dom(y) ≡ high → c ≡ d → (if x == y then a else c) ≡ (if x == y then b else d)

confinment : ∀ {s₁ s₂ σ₁ σ₂} → [ high ]⊢ s₁
                             → ⟨ s₁ , σ₁ ⟩→⟨ s₂ , σ₂ ⟩
                             → σ₁ =ₗ σ₂
confinment skip (skip σ₂) = =ₗ-refl
confinment (asgnh x-high) (ass σ₁ x exp z x₂) = equal (λ y y-low → lemma y-low x-high)
confinment (seq type₁ type₂) (comp₁ σ₁ σ₂ s₁ s₂ exec)
  with confinment type₁ exec
... | equal x = equal x
confinment (seq type₁ type₂) (comp₂ σ₁ σ₂ s₁ s₁' s₂ exec)
  with confinment type₁ exec
... | equal x = equal x
confinment (while b-high type) (while₁ σ₂ s b b-true) = equal (λ x x-low → refl)
confinment (while b-high type) (while₂ σ₂ s b b-false) = equal (λ x x-low → refl)
confinment (ite x type₁ type₂) (if₁ σ₂ s₁ s₂ b x₁) = equal (λ x x-low → refl)
confinment (ite x type₁ type₂) (if₂ σ₂ s₁ s₂ b x₁) = equal (λ x x-low → refl)


high-typed-stmts : ∀ {s₁ s₂ σ₁ σ₂} → [ high ]⊢ s₁
                                   → ⟨ s₁ , σ₁ ⟩→⟨ s₂ , σ₂ ⟩
                                   → (∃ \ s₂' → s₂ ≡ inj₁ s₂' × [ high ]⊢ s₂') ⊎ s₂ ≡ inj₂ []
high-typed-stmts skip (skip σ₂) = inj₂ refl
high-typed-stmts (asgnh x-high) (ass σ₁ x exp z exp⇓) = inj₂ refl
high-typed-stmts (seq s₁-high s₂-high) (comp₁ σ₁ σ₂ s₁ s₂ e) = inj₁ (s₂ , refl , s₂-high)
high-typed-stmts (seq s₁-high s₂-high) (comp₂ σ₁ σ₂ s₁ s₁' s₂ e) --= inj₁ (comp s₁' s₂ , refl , {!!})
  with high-typed-stmts s₁-high e
... | inj₁ (.s₁' , refl , s₁'-high) = inj₁ (comp s₁' s₂ , refl , (seq s₁'-high s₂-high))
... | inj₂ ()
high-typed-stmts (while b-high s-high) (while₁ σ₂ s b x) = inj₁ (comp s while b do s od , refl , (seq s-high (while b-high s-high)))
high-typed-stmts (while b-high s-high) (while₂ σ₂ s b x) = inj₂ refl
high-typed-stmts (ite b-high s₁-high s₂-high) (if₁ σ₂ s₁ s₂ b x) = inj₁ (s₁ , refl , s₁-high)
high-typed-stmts (ite b-high s₁-high s₂-high) (if₂ σ₂ s₁ s₂ b x) = inj₁ (s₂ , refl , s₂-high)

confined-sequence : ∀ {s σ σ'} → ∀ n → [ high ]⊢ s → ⟨ inj₁ s , σ ⟩→ n ⟨ inj₂ [] , σ' ⟩ → σ =ₗ σ'
confined-sequence ℕ.zero s-high (next () step  n-steps)
confined-sequence (ℕ.suc n) s-high (next n>0 step n-steps)
  with confinment s-high step | high-typed-stmts s-high step
... | σ=ₗσ'' | inj₁ (s' , refl , s'-high)
  with confined-sequence n s'-high n-steps
... | σ''=ₗσ' = =ₗ-trans σ=ₗσ'' σ''=ₗσ'
confined-sequence (ℕ.suc .0) s-high (next n>0 step stop) | σ=ₗσ' | inj₂ refl = σ=ₗσ'

if-low-equal : ∀ {x σ σ' z z'} → (b : Bool) → σ =ₗ σ' → z ≡ z' → dom(x) ≡ low → (if b then z else σ x) ≡ (if b then z' else σ' x)
if-low-equal true l-equal z=z' x-low = z=z'
if-low-equal {x} false (equal f) z=z' x-low = f x x-low

soundness' : ∀ {pc s σ₁ σ₁' σ₂ σ₂'} → ∀ n m  → Acc _<′_ n → Acc _<′_ m
                                             → [ pc ]⊢ s
                                             → ⟨ inj₁ s , σ₁ ⟩→ n ⟨ inj₂ [] , σ₂ ⟩
                                             → ⟨ inj₁ s , σ₁' ⟩→ m ⟨ inj₂ [] , σ₂' ⟩
                                             → σ₁ =ₗ σ₁' → σ₂ =ₗ σ₂'
soundness' ℕ.zero m _ _ t (next () step n-steps) e₂ σ₁=ₗσ₁'
soundness' (ℕ.suc n) ℕ.zero x x₁ t e₁ (next () step m-steps) σ₁=ₗσ₁'
-- Case: skip
soundness' (ℕ.suc .0) (ℕ.suc .0) x x₁ skip (next n>0 (skip σ₁) stop) (next m>0 (skip σ₂) stop) σ₁=ₗσ₂ = σ₁=ₗσ₂
-- Case: sub
soundness' (ℕ.suc n) (ℕ.suc m) x x₁ (sub t) n-steps m-steps σ₁=ₗσ₁'
  with confined-sequence (ℕ.suc n) t n-steps | confined-sequence (ℕ.suc m) t m-steps
... | σ₁=ₗσ₂ | σ₁'=ₗσ₂' = =ₗ-trans (=ₗ-sym σ₁=ₗσ₂) (=ₗ-trans σ₁=ₗσ₁' σ₁'=ₗσ₂')
-- Case: asgnh
soundness' (ℕ.suc 0) (ℕ.suc 0) _ _ (asgnh x-high) (next n>0 (ass σ₁ x exp z x₃) stop)
                                                  (next m>0 (ass σ₁' .x .exp z₁ x₄) stop) (equal σ₁=ₗσ₁')
                                                  = equal (λ y y-low → lemma2 y-low x-high (σ₁=ₗσ₁' y y-low))
-- Case: asgnl
soundness' (ℕ.suc 0) (ℕ.suc 0) _ _ (asgnl x-low) (next n>0 (ass σ₁ x exp z x₃) stop)
                                                 (next m>0 (ass σ₁' .x .exp z' x₄) stop) σ₁=ₗσ₁'
  with simple-security-aexp x-low σ₁=ₗσ₁' x₃ x₄
... | z=z' = equal (λ y y-low → if-low-equal (y == x) σ₁=ₗσ₁' z=z' y-low)
-- Case: seq
soundness' (ℕ.suc n) (ℕ.suc m) (acc f) (acc g) (seq t₁ t₂) n-steps m-steps σ₁=ₗσ₁'
  with seq-decomp (ℕ.suc n) n-steps | seq-decomp (ℕ.suc m) m-steps
... | k , l , _ , s₁ , s₂ , k<n , l<n | i , h , _ , s₁' , s₂' , i<n , h<n
  with soundness' k i (f k k<n) (g i i<n) t₁ s₁ s₁' σ₁=ₗσ₁'
... | σ=ₗσ'
  with soundness' l h (f l l<n) (g h h<n) t₂ s₂ s₂' σ=ₗσ'
... | σ₂=ₗσ₂' = σ₂=ₗσ₂'
-- Case while
soundness' {low} (ℕ.suc n) (ℕ.suc m) (acc f) (acc g) (while b-low s-low) (next n>0 (while₁ σ s b b⇓) n-steps)
                                                             (next m>0 (while₁ σ' .s .b b⇓') m-steps) σ₁=ₗσ₁'
  with soundness' n m (f n ≤′-refl) (g m ≤′-refl) (seq s-low (while b-low s-low)) n-steps m-steps σ₁=ₗσ₁'
... | σ₂=ₗσ₂' = σ₂=ₗσ₂'
soundness' {low} (ℕ.suc n) (ℕ.suc m) _ _ (while b-low s-low) (next n>0 (while₁ σ s b b⇓) n-steps)
                                                             (next m>0 (while₂ σ' .s .b b⇓') m-steps) σ₁=ₗσ₁'
  with simple-security-bexp b-low σ₁=ₗσ₁' b⇓ b⇓'
... | ()                                
soundness' {low} (ℕ.suc n) (ℕ.suc m) _ _ (while b-low s-low) (next n>0 (while₂ σ s b b⇓) n-steps)
                                                             (next m>0 (while₁ σ' .s .b b⇓') m-steps) σ₁=ₗσ₁'
  with simple-security-bexp b-low σ₁=ₗσ₁' b⇓ b⇓'
... | ()
soundness' {low} (ℕ.suc 0) (ℕ.suc 0) _ _ (while b-low s-low) (next n>0 (while₂ σ s b b⇓) stop)
                                                             (next m>0 (while₂ σ' .s .b b⇓') stop) σ₁=ₗσ₁ = σ₁=ₗσ₁
soundness' {high} (ℕ.suc n) (ℕ.suc m) _ _ (while b-high s-high) n-steps m-steps σ₁=ₗσ₁'
  with confined-sequence (ℕ.suc n) (while b-high s-high) n-steps | confined-sequence (ℕ.suc m) (while b-high s-high) m-steps
... | σ₁=ₗσ₂ | σ₁'=ₗσ₂' = =ₗ-trans (=ₗ-sym σ₁=ₗσ₂) (=ₗ-trans σ₁=ₗσ₁' σ₁'=ₗσ₂')
-- Case: ite
soundness' {low} (ℕ.suc n) (ℕ.suc m) (acc f) (acc g) (ite b-low s₁-low s₂-low) (next n>0 (if₁ σ s₁ s₂ b b⇓) n-steps)
                                                                               (next m>0 (if₁ σ' .s₁ .s₂ .b b⇓') m-steps) σ₁=ₗσ₁'
  with soundness' n m (f n ≤′-refl) (g m ≤′-refl) s₁-low n-steps m-steps σ₁=ₗσ₁'
... | σ₂=ₗσ₂' = σ₂=ₗσ₂'
soundness' {low} (ℕ.suc n) (ℕ.suc m) (acc f) (acc g) (ite b-low s₁-low s₂-low) (next n>0 (if₂ σ s₁ s₂ b b⇓) n-steps)
                                                                               (next m>0 (if₂ σ' .s₁ .s₂ .b b⇓') m-steps) σ₁=ₗσ₁'
  with soundness' n m (f n ≤′-refl) (g m ≤′-refl) s₂-low n-steps m-steps σ₁=ₗσ₁'
... | σ₂=ₗσ₂' = σ₂=ₗσ₂'
soundness' {low} (ℕ.suc n) (ℕ.suc m) (acc f) (acc g) (ite b-low s₁-low s₂-low) (next n>0 (if₁ σ s₁ s₂ b b⇓) n-steps)
                                                                               (next m>0 (if₂ σ' .s₁ .s₂ .b b⇓') m-steps) σ₁=ₗσ₁'
  with simple-security-bexp b-low σ₁=ₗσ₁' b⇓ b⇓'
... | ()
soundness' {low} (ℕ.suc n) (ℕ.suc m) (acc f) (acc g) (ite b-low s₁-low s₂-low) (next n>0 (if₂ σ s₁ s₂ b b⇓) n-steps)
                                                                               (next m>0 (if₁ σ' .s₁ .s₂ .b b⇓') m-steps) σ₁=ₗσ₁'
  with simple-security-bexp b-low σ₁=ₗσ₁' b⇓ b⇓'
... | ()
soundness' {high} (ℕ.suc n) (ℕ.suc m) x x₁ (ite b-high s₁-high s₂-high) n-steps m-steps σ₁=ₗσ₁'
  with confined-sequence (ℕ.suc n) (ite b-high s₁-high s₂-high) n-steps | confined-sequence (ℕ.suc m) (ite b-high s₁-high s₂-high) m-steps
... | σ₁=ₗσ₂ | σ₁'=ₗσ₂' = =ₗ-trans (=ₗ-sym σ₁=ₗσ₂) (=ₗ-trans σ₁=ₗσ₁' σ₁'=ₗσ₂')

soundness : ∀ {pc s} → [ pc ]⊢ s → noninterferent s
soundness typeable = yes (λ {σ₁ σ₁' σ₂ σ₂' l-equal (eval {n} n-steps) (eval {m} m-steps)
                           → soundness' n m (<-well-founded n) (<-well-founded m) typeable n-steps m-steps l-equal})
