{-# OPTIONS --cubical --guarded #-}
module Main where


--Primitives for guarded recursion
import LaterPrims

-- The guarded recursive type of branching streams.
import BranchingStreams

S = BranchingStreams.S
mapS = BranchingStreams.mapS
mapS-id = BranchingStreams.mapS-id

-- The countable powerset monad as a HIT.
import CountablePowerSet 

P∞ = CountablePowerSet.P∞
_∪_ = CountablePowerSet._∪_
IndP∞ = CountablePowerSet.IndP∞
mapP∞ = CountablePowerSet.mapP∞
_∈_ = CountablePowerSet._∈_
∈mapP∞-eq = CountablePowerSet.∈mapP∞-eq

-- Abstract names.
import AbsNames

lift = AbsNames.OpNames.lift
snoc = AbsNames.OpNames.snoc
swap = AbsNames.OpNames.swap




-- ============== Fully abstract model of CCS =======================
module CCS where

  -- The syntax of CCS, structural congruence, operational semantics.
  import ccs.Syntax

  Act = ccs.Syntax.Act
  CCS = ccs.Syntax.CCS
  mapAct = ccs.Syntax.mapAct
  mapCCS = ccs.Syntax.mapCCS
  _≈_ = ccs.Syntax._≈_
  _[_]↦_ = ccs.Syntax._[_]↦_

  -- Notions of algebra and model for CCS.
  import ccs.Algebra

  isCCS-alg = ccs.Algebra.isCCS-alg
  StructCong = ccs.Algebra.StructCong
  OpSem = ccs.Algebra.Dynamics
  isCCS-model = ccs.Algebra.isCCS-model

  -- Bisimilarity.
  import ccs.Bisim

  BisimT = ccs.Bisim.BisimRel.Bisim
  
  -- Semantic processes and their algebra structure.
  import ccs.semantics.Algebra
 
  F = ccs.semantics.Algebra.F
  Step = ccs.semantics.Algebra.Step
  Proc = ccs.semantics.Algebra.Proc
  mapProc = ccs.semantics.Algebra.mapProc-Inj

  endProc = ccs.semantics.Algebra.endProc
  sumProc = ccs.semantics.Algebra.sumProc
  actProc = ccs.semantics.Algebra.actProc
  parProc = ccs.semantics.Algebra.parProc
  νProc = ccs.semantics.Algebra.νProc
  !Proc = ccs.semantics.Algebra.!Proc

  -- Lemmata about mapProc.
  import ccs.semantics.MapProcLemmata

  par-map = ccs.semantics.MapProcLemmata.par-map

  -- Equality in Proc is closed under structural congruence.
  import ccs.semantics.StructuralCongruence

  ProcStructCong = ccs.semantics.StructuralCongruence.ProcStructCong

  -- Modelling reduction in Proc.
  import ccs.semantics.Dynamics

  ProcOpSem = ccs.semantics.Dynamics.ProcDynamics

  -- The CCS-model structure on Proc.
  import ccs.semantics.Model

  ProcModel = ccs.semantics.Model.ProcModel

  -- Syntactic processes have an F-coalgebra structure.
  import ccs.semantics.Coalgebra

  step = ccs.semantics.Coalgebra.CoalgebraCCS.step
  _≈∈≈step_ = ccs.semantics.Coalgebra._≈∈≈step_
  opsem-eq = ccs.semantics.Coalgebra.opsem-eq
  eval = ccs.semantics.Coalgebra.Eval.eval

  -- Full abstraction.
  import ccs.semantics.FullAbstraction

  fullAbstract = ccs.semantics.FullAbstraction.fullAbstract




-- ============== Fully abstract model of ealy π-calculus ===================
module Pi where

  -- The syntax of π-calculus, structural congruence, early operational semantics.
  import pi-calculus.Syntax

  Act = pi-calculus.Syntax.Act
  Pi = pi-calculus.Syntax.Pi
  mapPi = pi-calculus.Syntax.mapPi
  _≈_ = pi-calculus.Syntax._≈_
  _[_]↦_ = pi-calculus.Syntax._[_]↦_

  -- Notions of algebra and model of the early π-calculus.
  import pi-calculus.Algebra

  isPi-alg = pi-calculus.Algebra.isPi-alg
  StructCong = pi-calculus.Algebra.StructCong
  OpSem = pi-calculus.Algebra.Dynamics
  isPi-model = pi-calculus.Algebra.isPi-model

  -- Bisimilarity.
  import pi-calculus.Bisim

  BisimT = pi-calculus.Bisim.BisimRel.Bisim

  -- Semantic processes and their algebra structure.
  import pi-calculus.semantics.Algebra
 
  F = pi-calculus.semantics.Algebra.F
  Step = pi-calculus.semantics.Algebra.Step
  Proc = pi-calculus.semantics.Algebra.Proc
  mapProc = pi-calculus.semantics.Algebra.mapProc-Inj

  endProc = pi-calculus.semantics.Algebra.endProc
  sumProc = pi-calculus.semantics.Algebra.sumProc
  actProc = pi-calculus.semantics.Algebra.actProc
  parProc = pi-calculus.semantics.Algebra.parProc
  νProc = pi-calculus.semantics.Algebra.νProc
  !Proc = pi-calculus.semantics.Algebra.!Proc
  guardProc = pi-calculus.semantics.Algebra.guardProc

  -- Lemmata about mapProc.
  import pi-calculus.semantics.MapProcLemmata

  par-map = pi-calculus.semantics.MapProcLemmata.par-map

  -- Equality in Proc is closed under structural congruence.
  -- NB: stepν-swap has to be proved!!!
  import pi-calculus.semantics.StructuralCongruence

  ProcStructCong = pi-calculus.semantics.StructuralCongruence.ProcStructCong

  -- Modelling reduction in Proc.
  import pi-calculus.semantics.Dynamics

  ProcOpSem = pi-calculus.semantics.Dynamics.ProcDynamics

  -- The Pi-model structure on PiMod.
  import pi-calculus.semantics.Model

  PiMod-model = pi-calculus.semantics.Model.PiMod-model

  -- Syntactic processes have an F-coalgebra structure.
  import pi-calculus.semantics.Coalgebra

  step = pi-calculus.semantics.Coalgebra.CoalgebraPi.step
  _≈∈≈step_ = pi-calculus.semantics.Coalgebra._≈∈≈step_
  opsem-eq = pi-calculus.semantics.Coalgebra.opsem-eq
  eval = pi-calculus.semantics.Coalgebra.Eval.eval

  -- Full abstraction.
  import pi-calculus.semantics.FullAbstraction

  fullAbstract = pi-calculus.semantics.FullAbstraction.fullAbstract

