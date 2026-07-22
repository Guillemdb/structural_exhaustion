import Hypostructure.Core.Metadata
import Hypostructure.Core.Residual.ProofProjection
import Hypostructure.Graph.BoundaryOverlap

/-!
# Graph-local atom replacement

This module packages the reusable replacement pattern for a proper
boundaried atom.  The application supplies only the semantic replacement
certificate for its target and baseline; Graph derives the glued strict
progress and Core minimality contradiction.
-/

namespace Hypostructure.Graph

open Hypostructure

universe u v uPrevious

/-- A same-interface replacement certificate for one proper atom.

The fields are the graph-generic form of the replacement lemma hypotheses:
same boundary-degree fibre, unchanged boundary-overlap count against the
literal context, a baseline glued replacement, target-response domination,
and strict local progress. -/
structure AtomReplacementCertificate
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState))
    (atom : ProperBoundariedAtom ctx.G)
    (replacement : BoundaryPiece atom.decomposition.interface) where
  boundaryDegree_eq :
    replacement.boundaryDegreeProfile =
      atom.decomposition.piece.boundaryDegreeProfile
  overlapCount_eq :
    boundaryOverlapEdgeCount replacement atom.decomposition.outside =
      boundaryOverlapEdgeCount atom.decomposition.piece atom.decomposition.outside
  baseline :
    Baseline (glue replacement atom.decomposition.outside)
  target_le :
    Target (glue replacement atom.decomposition.outside) ->
      Target (glue atom.decomposition.piece atom.decomposition.outside)
  locallySmaller :
    replacement.LocallySmaller atom.decomposition.piece

namespace AtomReplacementCertificate

variable {Baseline : FiniteObject.{u} -> Prop}
variable {BranchState : FiniteObject.{u} -> Type v}
variable {Target : FiniteObject.{u} -> Prop}
variable {ctx : Core.MinimalCounterexampleContext
  (problem Baseline BranchState) Target
  (lexicographicProgress Baseline BranchState)}
variable {atom : ProperBoundariedAtom ctx.G}
variable {replacement : BoundaryPiece atom.decomposition.interface}

/-- The glued replacement is strictly smaller than the ambient graph. -/
theorem gluedReplacement_smaller
    (certificate : AtomReplacementCertificate ctx atom replacement) :
    (lexicographicProgress Baseline BranchState).Smaller
      (glue replacement atom.decomposition.outside) ctx.G := by
  have smallerSource :
      (glue replacement atom.decomposition.outside).LexicographicallySmaller
        (glue atom.decomposition.piece atom.decomposition.outside) :=
    glue_lexicographicallySmaller_of_local_of_overlapCount_eq
      atom.decomposition.outside certificate.locallySmaller
      certificate.overlapCount_eq
  have sourceIso :
      (glue atom.decomposition.piece atom.decomposition.outside).Isomorphic
        ctx.G :=
    ⟨atom.decomposition.reconstructionIso⟩
  exact
    (FiniteObject.lexicographicallySmaller_congr_right sourceIso).mp
      smallerSource

/-- A replacement certificate contradicts the inherited minimal
counterexample context. -/
theorem impossible
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (certificate : AtomReplacementCertificate ctx atom replacement) :
    False := by
  have replacementTarget :
      Target (glue replacement atom.decomposition.outside) :=
    ctx.target_of_smaller certificate.gluedReplacement_smaller
      certificate.baseline
  have sourceTarget :
      Target (glue atom.decomposition.piece atom.decomposition.outside) :=
    certificate.target_le replacementTarget
  have sourceIso :
      (glue atom.decomposition.piece atom.decomposition.outside).Isomorphic
        ctx.G :=
    ⟨atom.decomposition.reconstructionIso⟩
  exact ctx.avoids (targetInvariant.transport sourceIso sourceTarget)

end AtomReplacementCertificate

/-- The replacement statement over the active residual selected by a focus. -/
abbrev FocusedAtomReplacementClaim
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (stage : Previous) (active : focus.Active stage) : Prop :=
  let ctx := context.read stage active
  forall (atom : ProperBoundariedAtom ctx.G)
    (replacement : BoundaryPiece atom.decomposition.interface),
      AtomReplacementCertificate ctx atom replacement -> False

/-- Graph-owned projection from replacement certificates to the minimality
contradiction on the literal active predecessor. -/
def focusedAtomReplacementProjectionQuery
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (targetInvariant : FiniteObject.IsomorphismInvariant Target) :
    Core.Residual.Focus.ActiveQuery focus
      (FocusedAtomReplacementClaim focus context) :=
  context.map fun _stage _active _ctx _atom _replacement certificate =>
    certificate.impossible targetInvariant

/-- Exact accumulated successor carrying the replacement contradiction. -/
abbrev FocusedAtomReplacementStage
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :=
  Core.Residual.ProofProjection.Stage focus
    (FocusedAtomReplacementClaim focus context)

/-- Counted focused replacement execution.  Core owns the active/inactive
routing and ledger extension; Graph owns the replacement contradiction. -/
def executeFocusedAtomReplacementCounted
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (previous : Previous) :
    Core.Counted (FocusedAtomReplacementStage focus context) :=
  Core.Residual.ProofProjection.executeCounted focus
    (FocusedAtomReplacementClaim focus context)
    (focusedAtomReplacementProjectionQuery focus context targetInvariant)
    previous

/-- Public focused replacement successor. -/
def executeFocusedAtomReplacement
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (previous : Previous) :
    FocusedAtomReplacementStage focus context :=
  (executeFocusedAtomReplacementCounted focus context targetInvariant previous).value

/-- Query the replacement contradiction from the newest focused extension. -/
def focusedAtomReplacementQuery
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState))) :
    Core.Residual.Focus.ActiveQuery
      (Core.Residual.ProofProjection.Profile focus
        (FocusedAtomReplacementClaim focus context))
      (fun stage active =>
        FocusedAtomReplacementClaim focus context stage.previous active) :=
  Core.Residual.ProofProjection.latestClaim focus
    (FocusedAtomReplacementClaim focus context)

@[simp] theorem executeFocusedAtomReplacementCounted_checks
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (previous : Previous) :
    (executeFocusedAtomReplacementCounted focus context targetInvariant
      previous).checks = focus.selectionBudget.checks previous := by
  change
    (Core.Residual.ProofProjection.executeCounted focus
      (FocusedAtomReplacementClaim focus context)
      (focusedAtomReplacementProjectionQuery focus context targetInvariant)
      previous).checks = focus.selectionBudget.checks previous
  rw [Core.Residual.ProofProjection.executeCounted_checks]

theorem executeFocusedAtomReplacementCounted_checks_bounded
    {Previous : Type uPrevious}
    (focus : Core.Residual.Focus.Profile Previous)
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (context : Core.Residual.Focus.ActiveQuery focus
      (fun _previous _active =>
        Core.MinimalCounterexampleContext
          (problem Baseline BranchState) Target
          (lexicographicProgress Baseline BranchState)))
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (previous : Previous) :
    (executeFocusedAtomReplacementCounted focus context targetInvariant
      previous).checks <=
        (Core.Residual.ProofProjection.workBudget focus).coefficient *
          ((Core.Residual.ProofProjection.workBudget focus).size previous + 1) ^
            (Core.Residual.ProofProjection.workBudget focus).degree :=
  Core.Residual.ProofProjection.executeCounted_checks_bounded focus
    (FocusedAtomReplacementClaim focus context)
    (focusedAtomReplacementProjectionQuery focus context targetInvariant)
    previous

end Hypostructure.Graph
