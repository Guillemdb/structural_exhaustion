import Hypostructure.Graph.Replacement
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

universe u w

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

/-- Contract-level counterexample predicate carried by the node-2 positive
branch. -/
def EGCounterexample (residual : EGInitialResidual.{u}) : Prop :=
  EGBaseline residual.object ∧ Not (EGTarget residual.object)

/-- Contract-level non-counterexample predicate carried by the node-2
negative branch. -/
def EGNotCounterexample (residual : EGInitialResidual.{u}) : Prop :=
  EGTarget residual.object

/-- Read the graph object from a focused query for the root residual. -/
def egInitialObjectActiveQuery
    {Previous : Type w} (focus : Core.Residual.Focus.Profile Previous)
    (residual : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => EGInitialResidual.{u})) :
    Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => EGAmbient.{u}) :=
  residual.map fun _previous _active root => root.object

/-- Read the baseline proof from a focused query for the root residual. -/
def egInitialBaselineActiveQuery
    {Previous : Type w} (focus : Core.Residual.Focus.Profile Previous)
    (residual : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => EGInitialResidual.{u})) :
    Core.Residual.Focus.ActiveQuery focus
      (fun previous active =>
        EGBaseline (residual.read previous active).object) :=
  residual.dependentMap fun _previous _active root => by
    simpa [EGBaseline, problem] using root.baseline

/-- Read target avoidance from the contract-level counterexample proof. -/
def egCounterexampleAvoidsActiveQuery
    {Previous : Type w} (focus : Core.Residual.Focus.Profile Previous)
    (residual : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active => EGInitialResidual.{u}))
    (counterexample : Core.Residual.Focus.ActiveQuery focus
      (fun previous active =>
        EGCounterexample (residual.read previous active))) :
    Core.Residual.Focus.ActiveQuery focus
      (fun previous active =>
        Not (EGTarget (residual.read previous active).object)) :=
  counterexample.map fun _previous _active proof => proof.2

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

/-- EG instantiation of Graph's normalized replacement profile.

The threshold `3` belongs to the registered Problem-64 baseline; Graph owns
the normalized gluing transfer and replacement executor. -/
def egNormalizedAtomReplacementProfile :
    Graph.NormalizedAtomReplacementProfile EGBaseline where
  LocalBaseline := fun {boundary} piece =>
    piece.InternalThresholdBaseline 3
  baselinePreserved := by
    intro boundary source replacement boundaryNonempty outside noBoundaryEdges degreeEq
      localBaseline sourceBaseline
    simpa [EGBaseline, Baseline] using
      Graph.glue_minDegree_ge_of_local_boundary_eq_of_context_noBoundaryEdges
        3 outside boundaryNonempty noBoundaryEdges degreeEq localBaseline
        sourceBaseline

end HypostructureErdos64EG
