open import Level
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.List renaming (_∷_ to _∥_)
open import Relation.Binary.Core

module OperationalSemantics (Var : Set) (_==_ : Var → Var → Bool) where

data AExp : Set where
  var : Var → AExp
  num : ℕ → AExp
  opₐ : AExp → AExp → AExp

data BExp : Set where
  true : BExp
  false : BExp
  ¬ : BExp → BExp
  opₚ : BExp → BExp → BExp
  opᵣ : AExp → AExp → BExp

data Exp : Set where
  skip : Exp
  ass : Var → AExp → Exp
  comp : Exp → Exp → Exp
  if_then_else_fi : BExp → Exp → Exp → Exp
  while_do_od : BExp → Exp → Exp
  spawn[_] : List Exp → Exp

data Stop : Set where
  [] : Stop

State = Var → ℕ
Config = (Exp ⊎ Stop) × State
SVec = List Exp
GConf = List Exp × State

data _⇓₁_ : AExp × State → ℕ → Set where
  var : ∀ x σ → (var x , σ) ⇓₁ σ x
  num : ∀ n σ → (num n , σ) ⇓₁ n
  op : ∀ a₁ a₂ σ n m → (a₁ , σ) ⇓₁ n → (a₂ , σ) ⇓₁ m → (opₐ a₁ a₂ , σ) ⇓₁ m

data _⇓₂_ : BExp × State → Bool → Set where
  true : ∀ σ → (true , σ) ⇓₂ true
  false : ∀ σ → (false , σ) ⇓₂ false
  ¬ : ∀ σ b t → (b , σ) ⇓₂ t → (¬ b , σ) ⇓₂ not t
  opₚ : ∀ σ b₁ b₂ t₁ t₂ → (b₁ , σ) ⇓₂ t₁ → (b₂ , σ) ⇓₂ t₂ → (opₚ b₁ b₂ , σ) ⇓₂ t₁
  opᵣ : ∀ σ a₁ a₂ z₁ z₂ → (a₁ , σ) ⇓₁ z₁ → (a₂ , σ) ⇓₁ z₂ → (opᵣ a₁ a₂ , σ) ⇓₂ true

record Eval (e : Set) (v : Set) : Set₁ where
  field _⇓_ : e × State → v → Set
  
evalAExp : Eval AExp ℕ
evalAExp = record { _⇓_ = _⇓₁_ }

evalBExp : Eval BExp Bool
evalBExp = record { _⇓_ = _⇓₂_ }

_⇓_ : {e v : Set} → {{eval : Eval e v}} → e × State → v → Set
_⇓_ {{eval}} = Eval._⇓_ eval

data ⟨_⟩→_⟨_⟩ : Exp × State → SVec → Config → Set where
  skip   : ∀ σ → ⟨ skip , σ ⟩→ [] ⟨ inj₂ [] , σ ⟩
  ass    : ∀ σ v a z → (a , σ) ⇓₁ z → ⟨ ass v a , σ ⟩→ [] ⟨ inj₂ [] , (λ x → if x == v then z else (σ x)) ⟩
  comp₁  : ∀ σ σ' s₁ s₂ α → ⟨ s₁ , σ ⟩→ α ⟨ inj₂ [] , σ' ⟩ → ⟨ comp s₁ s₂ , σ ⟩→ α ⟨ inj₁ s₂ , σ' ⟩
  comp₂  : ∀ σ σ' s₁ s₁' s₂ α → ⟨ s₁ , σ ⟩→ α ⟨ inj₁ s₁' , σ' ⟩ → ⟨ comp s₁ s₂ , σ ⟩→ α ⟨ inj₁ (comp s₁' s₂) , σ' ⟩
  if₁    : ∀ σ s₁ s₂ b → (b , σ) ⇓₂ true → ⟨ if b then s₁ else s₂ fi , σ ⟩→ [] ⟨ inj₁ s₁ , σ ⟩
  if₂    : ∀ σ s₁ s₂ b → (b , σ) ⇓₂ false → ⟨ if b then s₁ else s₂ fi , σ ⟩→ [] ⟨ inj₁ s₂ , σ ⟩
  while₁ : ∀ σ s b → (b , σ) ⇓₂ true → ⟨ while b do s od , σ ⟩→ [] ⟨ inj₁ (comp s (while b do s od)) , σ ⟩
  while₂ : ∀ σ s b → (b , σ) ⇓₂ false → ⟨ while b do s od , σ ⟩→ [] ⟨ inj₂ [] , σ ⟩
  spawn  : ∀ σ ls → ⟨ spawn[ ls ] , σ ⟩→ ls ⟨ inj₂ [] , σ ⟩

lookup : {A : Set} (xs : List A) → (n : ℕ) → n < length xs → A
lookup [] n ()
lookup (x ∥ xs) ℕ.zero p = x
lookup (x ∥ xs) (ℕ.suc n) (s≤s p) = lookup xs n p

replace : {A : Set} (xs : List A) → (i : ℕ) → (x : A) → List A → i < length xs → List A
replace xs i x ys p = take i xs ++ [ x ] ++ ys ++ drop i xs

data ⟨_⟩→⟨_⟩ : GConf → GConf → Set where
  sys : ∀ i L L' S σ σ' → (p : i < length L) → ⟨ lookup L i p , σ ⟩→ L' ⟨ inj₁ S , σ' ⟩ → ⟨ L , σ ⟩→⟨ replace L i S L' p , σ' ⟩
