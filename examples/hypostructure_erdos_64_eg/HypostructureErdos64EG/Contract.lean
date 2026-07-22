import Hypostructure.Graph.Progress
import HypostructureErdos64EG.InitialResidual

/-!
# Erdős--Gyárfás Problem 64 contract

This module is the public problem-level API for the Hypostructure EG
application.  It does not introduce new mathematics or rewrite node state; it
only names the framework classes and graph interfaces instantiated by
`Problem.lean` and the root residual.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Public name for the theorem-root packed graph type. -/
abbrev EGAmbient : Type (u + 1) :=
  Graph.FiniteObject.{u}

/-- Public name for the EG baseline predicate. -/
abbrev EGBaseline : EGAmbient.{u} -> Prop :=
  Baseline

/-- Public name for the EG branch state family. -/
abbrev EGBranchState : EGAmbient.{u} -> Type :=
  BranchState

/-- Public name for the registered Core problem. -/
abbrev EGProblem : Core.Problem :=
  problem

/-- Public name for the dyadic-cycle target predicate. -/
abbrev EGTarget : EGAmbient.{u} -> Prop :=
  Target

/-- Public name for the root theorem input residual. -/
abbrev EGInitialResidual :=
  InitialResidual.{u}

/-- Public name for the initial framework-owned residual stage. -/
abbrev EGInitialStage :=
  InitialStage.{u}

/-- Public name for the graph isomorphism-invariance of the baseline. -/
abbrev EGBaselineIsomorphismInvariant :
    Graph.FiniteObject.IsomorphismInvariant EGBaseline :=
  baselineIsomorphismInvariant

/-- Public name for the graph-isomorphism semantics used by EG. -/
abbrev EGIsomorphismSemantics : Core.SemanticEquivalence EGProblem :=
  isomorphismSemantics

/-- Public name for the dyadic-cycle target interface. -/
abbrev EGTargetInterface : Graph.TargetInterface EGTarget :=
  targetInterface

/-- Public name for the graph isomorphism-invariance of the target. -/
abbrev EGTargetIsomorphismInvariant :
    Graph.FiniteObject.IsomorphismInvariant EGTarget :=
  targetIsomorphismInvariant

/-- Public name for target invariance under the registered semantics. -/
abbrev EGTargetInvariant :
    Core.TargetInvariant EGIsomorphismSemantics EGTarget :=
  targetInvariant

/-- Public name for the lexicographic graph progress relation used by EG. -/
abbrev EGProgress :=
  Graph.lexicographicProgress EGBaseline EGBranchState

end HypostructureErdos64EG
