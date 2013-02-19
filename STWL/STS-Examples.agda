module STS-Examples where

open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Relation.Binary.Core

open import Domain
open import STWL

data Var : Set where
  l : ℕ → Var
  h : ℕ → Var

postulate _==_ : Var → Var → Bool

dom : Var → Dom
dom (l i) = low
dom (h i) = high

-- Some abbriviations
l₁ = l 1
l₂ = l 2
h₁ = h 1
h₂ = h 2

open import STS Var dom _==_

example₁ : [ low ]⊬ ass l₁ (opa (var h₁) (var l₂))
example₁ (sub (asgnh ()))
example₁ (asgnh ())
example₁ (asgnl (opa (var ()) (var x)))

example₂ : [ high ]⊢ if (opr (var h₂) (num 0)) then (ass h₂ (num 0)) else (ass h₂ (num 1)) fi
example₂ = ite highb (asgnh refl) (asgnh refl)

example₃ : [ low ]⊢ ass h₁ (opa (var l₁) (var l₂))
example₃ = asgnh refl

example₄ : [ low ]⊢ ass l₁ (opa (var l₁) (var l₂))
example₄ = asgnl (opa (var refl) (var refl))

example₅ : ⊢ aexp (opa (opa (var l₁) (num 5)) (var l₂)) ∶ high
example₅ = higha

example₆ : ⊬ aexp (opa (opa (var h₁) (num 5)) (var l₂)) ∶ low
example₆ (opa (opa (var ()) num) (var l₂-low))