module Examples where

open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Product
open import Relation.Binary.Core

open import Level

open import Domain

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

open import MTWL Var _==_
open import TS Var dom _==_


data _R₁_ : Rel SVec Level.zero where
  sa : [ skip ] R₁ [ ass h₁ (opa (var h₂) (var l₁)) ]
  as : [ ass h₁ (opa (var h₂) (var l₁)) ] R₁ [ skip ]
  ee : [] R₁ []

example₁ : [ skip ] ≈ [ (ass h₁ (opa (var h₂) (var l₁))) ]
example₁ = contained _R₁_ (record { sym = λ { (skip ∷ []) (ass (h 1) (opa (var (h 2)) (var (l 1))) ∷ []) sa → as ;
                                              (ass (h 1) (opa (var (h 2)) (var (l 1))) ∷ []) .(skip ∷ []) as → sa ;
                                              [] [] ee → ee };
                                    len = λ { (skip ∷ []) .(ass (h 1) (opa (var (h 2)) (var (l 1))) ∷ []) sa → refl ;
                                              (ass (h 1) (opa (var (h 2)) (var (l 1))) ∷ []) (skip ∷ []) as → refl ;
                                              [] [] ee → refl };
                                    sim = λ { (skip ∷ []) (ass (h 1) (opa (var (h 2)) (var (l 1))) ∷ []) .[] .[] .σ₂ σ₂ σ₁' ℕ.zero p q (skip .σ₂) sa x₂ → [] , ([] , ({!!} , {!!})) ;
                                              (skip ∷ []) .(ass (h 1) (opa (var (h 2)) (var (l 1))) ∷ []) L S σ₁ σ₂ σ₁' (ℕ.suc i) (s≤s ()) q x sa x₂ ;

                                              (ass (h 1) (opa (var (h 2)) (var (l 1))) ∷ []) (skip ∷ []) L S σ₁ σ₂ σ₁' i p q x as x₂ → {!!} ;
                                              
                                              [] [] L S σ₁ σ₂ σ₁' i () () x ee x₂}}) sa
