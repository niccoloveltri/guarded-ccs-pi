
{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Sigma
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (lift;act)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Logic
open import Cubical.Relation.Nullary
open import Basic
open import AbsNames
open import LaterPrims hiding (_∙_)

module pi-calculus.Bisim (ns : Names) where

open Names ns
open OpNames ns
open import pi-calculus.Syntax ns

-- Bisimilarity for pi-calculus.

-- Notice that in the paper, bisimilarity wrt. a transition system T
-- is called BisimT T, while Bisim is reserved for bisimilarity
-- wrt. the early operational semantics.

-- The definition of bisimilarlty is the guarded variant of the usual
-- one: two processes are bisimilar if, whenever one makes an
-- "a"-labelled transition to another later-process, the other also
-- makes an "a"-labelled transition and the two resulting
-- later-process are later-bisimilar.
module BisimRel (T : ∀ {m n} (P : Pi m) (a : Label m n) (P' : ▹ Pi n) → Set) where

  record SimF (R : ▹ (∀ n → Pi n → Pi n → Set)) (n : ℕ) (p q : Pi n) : Set where
    constructor conS
    field
      sim : ∀ {m} (a : Label n m) (p' : ▹ Pi m) → T p a p'
          → ∥ Σ (▹ Pi m) (λ q' → T q a q'
              × ▸ (λ α → R α m (p' α) (q' α)) ) ∥₁

  open SimF

  record BisimF (R : ▹ (∀ n → Pi n → Pi n → Set)) (n : ℕ) (p q : Pi n) : Set where
    constructor conB
    field
      fwd : SimF R n p q
      bwd : SimF R n q p

  open BisimF

  record Bisim (n : ℕ) (p q : Pi n) : Set where
    inductive
    constructor con
    field
      uncon : BisimF (next Bisim) n p q

  open Bisim

  isPropSimF : ∀ {R m Q P} → isProp (SimF R m Q P)
  isPropSimF =
    isPropRetract sim
                  _
                  (λ _ → refl)
                  (isPropImplicitΠ (λ _ → isPropΠ3 (λ _ _ _ → isPropPropTrunc)))

  isPropBisim : ∀ {m P Q} → isProp (Bisim m P Q)
  isPropBisim =
    isPropRetract (\ bsim → bsim .uncon .fwd , bsim .uncon .bwd)
                  (λ (x : _ × _) → con (conB (x .fst) (x .snd)))
                  (\ _ → refl)
                  (isProp× isPropSimF isPropSimF)


-- Early congruence
  EarlyCong : ∀ {n} → Pi n → Pi n → Set
  EarlyCong P Q = ∀ m (σ : Name _ → Name m) → Bisim m (mapPi σ P) (mapPi σ Q)
