
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

module ccs.Bisim (ns : Names) where

open Names ns
open OpNames ns
open import ccs.Syntax ns

-- Bisimilarity for CCS.

-- Notice that in the paper, bisimilarity wrt. a transition system
-- TransPi is called BisimT TransPi, while Bisim is reserved for
-- bisimilarity wrt. the operational semantics on CCS.

-- Analogously to the type Proc of semantic processes, bisimilarity is
-- also a guarded recursive type. The definition is the guarded
-- variant of the usual one: two processes are bisimilar if, whenever
-- one makes an "a"-labelled transition to another later-process, the
-- other also makes an "a"-labelled transition and the two resulting
-- later-process are later-bisimilar.
module BisimRel (T : ∀ {n} (P : CCS n) (a : Act n) (P' : ▹ CCS n) → Set) where

  record SimF (R : ▹ (∀ n → CCS n → CCS n → Set)) (n : ℕ) (p q : CCS n) : Set where
    constructor conS
    field
      sim : (a : Act n) (p' : ▹ CCS n) → T p a p'
          → ∥ Σ (▹ CCS n) (λ q' → T q a q'
              × ▸ (λ α → R α n (p' α) (q' α)) ) ∥₁

  open SimF

  record BisimF (R : ▹ (∀ n → CCS n → CCS n → Set)) (n : ℕ) (p q : CCS n) : Set where
    constructor conB
    field
      fwd : SimF R n p q
      bwd : SimF R n q p

  open BisimF

  record Bisim (n : ℕ) (p q : CCS n) : Set where
    inductive
    constructor con
    field
      uncon : BisimF (next Bisim) n p q

  open Bisim

  isPropSimF : ∀ {R m Q P} → isProp (SimF R m Q P)
  isPropSimF = isOfHLevelRetract 1 (\ s → s .sim) _ (\ _ → refl) (hLevelPi 1 (\ x → hLevelPi 1 \ _ → hLevelPi 1 \ _ → squash₁))

  isPropBisim : ∀ {m P Q} → isProp (Bisim m P Q)
  isPropBisim = isOfHLevelRetract 1 (\ bsim → bsim .uncon .fwd , bsim .uncon .bwd) (λ (x : _ × _) → con (conB (x .fst) (x .snd)))
                                        (\ _ → refl) (isOfHLevelΣ 1 isPropSimF (\ _ → isPropSimF))

