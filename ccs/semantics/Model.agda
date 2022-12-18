{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Relation.Nullary
open import CountablePowerSet
open import Basic
open import AbsNames
open import LaterPrims hiding (_∙_)

module ccs.semantics.Model (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import ccs.Syntax ns
open import ccs.Algebra ns
open import ccs.semantics.Algebra ns
open import ccs.semantics.MapProcLemmata ns
open import ccs.semantics.StructuralCongruence ns
open import ccs.semantics.Dynamics ns

-- Putting all together, Proc forms a model of CCS.
ProcModel : isCCS-model Proc
ProcModel = record
               { algX = ProcCCS-alg
               ; mapX = mapProc-Inj _ _
               ; EqX = _≡_
               ; congX = ProcStructCong
               ; TransX = λ P a Q → (a , next Q) ← P
               ; dynX = ProcDynamics
               ; mapX-id = mapProc-id _
               ; mapX-∘ = mapmapProc _ _ _ _ _
               ; map-evalX = mapProc-evalX
               }
              

