open import Level
open import Data.Empty
open import Data.Bool
open import Data.Nat hiding(zero; _⊔_)
open import Data.Product
open import Data.Sum
open import Data.List
open import Relation.Binary.Core
open import Function.Injection

open import Induction.Nat
open import Induction.WellFounded

open import Domain

module SecurityTypeSystem (Var : Set) (dom : Var → Dom) (_==_ : Var → Var → Bool) where

open import OperationalSemantics Var  _==_ renaming (Exp to Stmt)

data Exp' : Set where
  aexp : AExp → Exp'
  bexp : BExp → Exp'

data ⊢_∶_ : Exp' → Dom → Set where
  num : ∀ {n} → ⊢ aexp (num n) ∶ low
  var : ∀ {x} → dom x ≡ low →  ⊢ aexp (var x) ∶ low
  opa : ∀ {a₁ a₂} → ⊢ (aexp a₁) ∶ low → ⊢ (aexp a₂) ∶ low → ⊢ aexp (opₐ a₁ a₂) ∶ low

  true  : ⊢ bexp true ∶ low
  false : ⊢ bexp false ∶ low
  ¬     : ∀ {b} → ⊢ (bexp b) ∶ low → ⊢ bexp (¬ b) ∶ low
  opb   : ∀ {b₁ b₂} → ⊢ (bexp b₁) ∶ low → ⊢ (bexp b₂) ∶ low → ⊢ bexp (opₚ b₁ b₂) ∶ low
  opr   : ∀ {a₁ a₂} → ⊢ (aexp a₁) ∶ low → ⊢ (aexp a₂) ∶ low → ⊢ bexp (opᵣ a₁ a₂) ∶ low
  higha : ∀ {a} → ⊢ (aexp a) ∶ high
  highb : ∀ {b} → ⊢ (bexp b) ∶ high

⊬_∶_ : Exp' → Dom → Set
⊬ exp ∶ d = ⊢ exp ∶ d → ⊥

data ⊢_ : Stmt → Set where
  skip  : ⊢ skip
  asgnh : ∀ {x exp} → dom x ≡ high → ⊢ (x ≔ exp)
  asgnl : ∀ {x exp} → ⊢ (aexp exp) ∶ low → ⊢ (x ≔ exp)
  seq   : ∀ {s₁ s₂} → ⊢ s₁ → ⊢ s₂ → ⊢ (comp s₁ s₂)
  while : ∀ {b s} → ⊢ (bexp b) ∶ low → ⊢ s → ⊢ (while b do s od)
  ite   : ∀ {b s₁ s₂} → ⊢ (bexp b) ∶ low → ⊢ s₁ → ⊢ s₂ → ⊢ if b then s₁ else s₂ fi

⊬_ : Stmt → Set
⊬ s = ⊢ s → ⊥

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

record slb {ℓ} (_R_ : Rel SVec ℓ) : Set ℓ where
  field
    sym : ∀ L L' → L R L' → L' R L
    len : ∀ L L' → L R L' → length L ≡ length L'
    sim : ∀ (L₁ L₁' L : SVec) (S : Stmt ⊎ Stop) (σ₁ σ₂ σ₁' : State) i (p : i < length L₁)
          → ⟨ lookup L₁ i p , σ₁ ⟩→ L ⟨ S , σ₂ ⟩ → L₁ R L₁' → σ₁ =ₗ σ₁'
          → ∃ \ (L' : SVec) → ∃ \ (S' : Stmt ⊎ Stop) →  ∃ \s → ∃ \ s' →  ∃ \ σ₂' → ∃ \ q →
              (⟨ lookup L₁' i q , σ₁' ⟩→ L' ⟨ S' , σ₂' ⟩
              × (S ≡ inj₂ [] ⊎ (S ≡ inj₁ s × S' ≡ inj₁ s' × [ s ] R [ s' ]))
              × L R L'
              × σ₂ =ₗ σ₂')

-- We have to pay attention that we only include normal relations,
-- otherwise we could also include _≈_ which is obviously not
-- intented and would lead to non-termination.
data _≈_ : Rel SVec (Level.suc Level.zero) where
   contained : ∀ {L L'} (_R_ : Rel SVec Level.zero) → slb _R_ → L R L' → L ≈ L'

   
≈-slb-sim : ∀ L₁ L₁' L S σ₁ σ₂ σ₁' i (p : i < length L₁) → ⟨ lookup L₁ i p , σ₁ ⟩→ L ⟨ S , σ₂ ⟩ → L₁ ≈ L₁' → σ₁ =ₗ σ₁'
            → ∃ \ L' →  ∃ \ S' → ∃ \ s →  ∃ \ s' → ∃ \ σ₂' → ∃ \q →
            ⟨ lookup L₁' i q , σ₁' ⟩→ L' ⟨ S' , σ₂' ⟩
            × (S ≡ inj₂ [] ⊎ S ≡ inj₁ s × S' ≡ inj₁ s' × [ s ] ≈ [ s' ])
            × L ≈ L' × σ₂ =ₗ σ₂'
≈-slb-sim L₁ L₁' L S σ₁ σ₂ σ₁' i p step (contained R slb L₁RL₁') σ₁=ₗσ₁'
  with slb.sim slb L₁ L₁' L S σ₁ σ₂ σ₁' i p step L₁RL₁' σ₁=ₗσ₁'
... | L' , S' , s , s' , σ₂' , q , L₁→S' , inj₁ S≡[] , LRL' , σ₂=ₗσ₂'
    = L' , S' , s , s' , σ₂' , q , L₁→S' , inj₁ S≡[] , contained R slb LRL' , σ₂=ₗσ₂'
... | L' , S' , s , s' , σ₂' , q , L₁→S' , inj₂ (S≡s , S'≡s' , sRs') , LRL' , σ₂=ₗσ₂'
    = L' , S' , s , s' , σ₂' , q , L₁→S' , inj₂ (S≡s , S'≡s' , contained R slb sRs') , contained R slb LRL' , σ₂=ₗσ₂'

≈-is-a-slb : slb _≈_
≈-is-a-slb = record { sym = λ {L L' (contained R s LRL') → contained R s (slb.sym s L L' LRL')};
                      len = λ {L L' (contained R s LRL') → slb.len s L L' LRL'};
                      sim = ≈-slb-sim }

-- ≈-not-refl : ∀ (L : SVec) → L ≈ L → ⊥
-- ≈-not-refl L L≈L = ?

-- ≈-trans : Transitive _≈_
-- ≈-trans L₁≈L₂ L₂≈L₃  = {!!}


module strong-security-skip where

  data _R_ : Rel SVec Level.zero where
    refl-skip : [ skip ] R [ skip ]
    empty     : [] R []

  ss-skip : [ skip ] ≈ [ skip ]
  ss-skip = contained _R_ (record { sym = λ { (skip ∷ []) (skip ∷ []) refl-skip → refl-skip;
                                              []          []          empty     → empty
                                            };
                                    len = λ { (skip ∷ []) (skip ∷ []) refl-skip → refl;
                                              []          []          empty     → refl
                                            };
                                    sim = λ { (skip ∷ []) (skip ∷ []) [] (inj₂ []) σ₁ .σ₁ σ₁' 0 p (skip .σ₁) refl-skip σ₁=ₗσ₁'
                                                → [] , (inj₂ []) , skip , skip , σ₁' , (s≤s z≤n) , skip σ₁' , inj₁ refl , empty , σ₁=ₗσ₁';
                                              [] [] L S σ₁ σ₂ σ₁' i () L₁→S empty σ₁=ₗσ₁';
                                              (skip ∷ []) (skip ∷ []) L (inj₁ S) σ₁ σ₂ σ₁' 0 p () refl-skip σ₁=ₗσ₁';
                                              (skip ∷ []) (skip ∷ []) (s ∷ ss) S σ₁ σ₂ σ₁' 0 p () refl-skip σ₁=ₗσ₁';
                                              (skip ∷ []) (skip ∷ []) L S σ₁ σ₂ σ₁' (ℕ.suc n) (s≤s ()) L₁→S refl-skip σ₁=ₗσ₁'
                                               }
                                   })
                      refl-skip
