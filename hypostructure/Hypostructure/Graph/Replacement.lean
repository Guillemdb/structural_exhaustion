import Hypostructure.Core.Metadata
import Hypostructure.Core.Residual.ProofProjection
import Hypostructure.Graph.AtomResponse
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

universe u v w uPrevious

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

/-- A proper atom whose outside context is normalized: all boundary--boundary
edges are owned by the atom side. -/
structure NormalizedProperBoundariedAtom (object : FiniteObject.{u}) where
  toAtom : ProperBoundariedAtom object
  boundaryNonempty : Nonempty toAtom.decomposition.interface.Vertex
  noBoundaryEdges :
    toAtom.decomposition.outside.NoBoundaryEdges

/-- Baseline preservation data for normalized boundaried replacement.

The graph layer owns the gluing and minimality argument; an application
instantiation supplies only the local replacement baseline and the theorem
that this local baseline preserves its registered graph baseline under
normalized gluing. -/
structure NormalizedAtomReplacementProfile
    (Baseline : FiniteObject.{u} -> Prop) where
  LocalBaseline :
    {boundary : Boundary.{u}} -> BoundaryPiece boundary -> Prop
  baselinePreserved :
    forall {boundary : Boundary.{u}}
      {source replacement : BoundaryPiece boundary}
      [Nonempty boundary.Vertex]
      (outside : OutsideContext boundary),
      outside.NoBoundaryEdges ->
      replacement.boundaryDegreeProfile = source.boundaryDegreeProfile ->
      LocalBaseline replacement ->
      Baseline (glue source outside) ->
      Baseline (glue replacement outside)

/-- The manuscript replacement certificate for normalized contexts.  It does
not ask the caller for an overlap count; Graph derives that count from
normalized boundary ownership. -/
structure NormalizedAtomReplacementCertificate
    {Baseline : FiniteObject.{u} -> Prop}
    {BranchState : FiniteObject.{u} -> Type v}
    {Target : FiniteObject.{u} -> Prop}
    (profile : NormalizedAtomReplacementProfile Baseline)
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState))
    (atom : NormalizedProperBoundariedAtom ctx.G)
    (replacement :
      BoundaryPiece atom.toAtom.decomposition.interface) where
  boundaryDegree_eq :
    replacement.boundaryDegreeProfile =
      atom.toAtom.decomposition.piece.boundaryDegreeProfile
  localBaseline :
    profile.LocalBaseline replacement
  target_le :
    Target (glue replacement atom.toAtom.decomposition.outside) ->
      Target (glue atom.toAtom.decomposition.piece
        atom.toAtom.decomposition.outside)
  locallySmaller :
    replacement.LocallySmaller atom.toAtom.decomposition.piece

namespace NormalizedAtomReplacementCertificate

variable {Baseline : FiniteObject.{u} -> Prop}
variable {BranchState : FiniteObject.{u} -> Type v}
variable {Target : FiniteObject.{u} -> Prop}
variable {profile : NormalizedAtomReplacementProfile Baseline}
variable {ctx : Core.MinimalCounterexampleContext
  (problem Baseline BranchState) Target
  (lexicographicProgress Baseline BranchState)}
variable {atom : NormalizedProperBoundariedAtom ctx.G}
variable {replacement :
  BoundaryPiece atom.toAtom.decomposition.interface}

/-- Graph converts a normalized-context replacement into the overlap-aware
generic certificate consumed by the existing minimality proof. -/
def toAtomReplacementCertificate
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (certificate :
      NormalizedAtomReplacementCertificate profile ctx atom replacement) :
    AtomReplacementCertificate ctx atom.toAtom replacement where
  boundaryDegree_eq := certificate.boundaryDegree_eq
  overlapCount_eq := by
    rw [boundaryOverlapEdgeCount_eq_zero_of_context_noBoundaryEdges
        replacement atom.toAtom.decomposition.outside atom.noBoundaryEdges,
      boundaryOverlapEdgeCount_eq_zero_of_context_noBoundaryEdges
        atom.toAtom.decomposition.piece atom.toAtom.decomposition.outside
        atom.noBoundaryEdges]
  baseline := by
    letI : Nonempty atom.toAtom.decomposition.interface.Vertex :=
      atom.boundaryNonempty
    have sourceIso :
        (glue atom.toAtom.decomposition.piece
          atom.toAtom.decomposition.outside).Isomorphic ctx.G :=
      ⟨atom.toAtom.decomposition.reconstructionIso⟩
    have sourceBaseline :
        Baseline (glue atom.toAtom.decomposition.piece
          atom.toAtom.decomposition.outside) :=
      (baselineInvariant.iff_of_iso sourceIso).mpr ctx.baseline
    exact profile.baselinePreserved atom.toAtom.decomposition.outside
      atom.noBoundaryEdges certificate.boundaryDegree_eq
      certificate.localBaseline sourceBaseline
  target_le := certificate.target_le
  locallySmaller := certificate.locallySmaller

/-- A normalized replacement certificate contradicts the inherited minimal
counterexample context. -/
theorem impossible
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (certificate :
      NormalizedAtomReplacementCertificate profile ctx atom replacement) :
    False :=
  (certificate.toAtomReplacementCertificate baselineInvariant).impossible
    targetInvariant

end NormalizedAtomReplacementCertificate

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

/-! ## Normalized-context focused replacement -/

/-- The normalized replacement statement over the active residual selected by
a focus. -/
abbrev FocusedNormalizedAtomReplacementClaim
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (stage : Previous) (active : focus.Active stage) : Prop :=
  let ctx := context.read stage active
  forall (atom : NormalizedProperBoundariedAtom ctx.G)
    (replacement : BoundaryPiece atom.toAtom.decomposition.interface),
      NormalizedAtomReplacementCertificate profile ctx atom replacement ->
        False

/-- Graph-owned projection from normalized replacement certificates to the
minimality contradiction on the literal active predecessor. -/
def focusedNormalizedAtomReplacementProjectionQuery
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target) :
    Core.Residual.Focus.ActiveQuery focus
      (FocusedNormalizedAtomReplacementClaim focus context profile) :=
  context.map fun _stage _active _ctx _atom _replacement certificate =>
    certificate.impossible baselineInvariant targetInvariant

/-- Exact accumulated successor carrying the normalized replacement
contradiction. -/
abbrev FocusedNormalizedAtomReplacementStage
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
    (profile : NormalizedAtomReplacementProfile Baseline) :=
  Core.Residual.ProofProjection.Stage focus
    (FocusedNormalizedAtomReplacementClaim focus context profile)

/-- Counted focused normalized replacement execution.  Core owns the
active/inactive routing and ledger extension; Graph owns normalized gluing,
baseline transfer, and the replacement contradiction. -/
def executeFocusedNormalizedAtomReplacementCounted
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (previous : Previous) :
    Core.Counted (FocusedNormalizedAtomReplacementStage focus context profile) :=
  Core.Residual.ProofProjection.executeCounted focus
    (FocusedNormalizedAtomReplacementClaim focus context profile)
    (focusedNormalizedAtomReplacementProjectionQuery focus context profile
      baselineInvariant targetInvariant)
    previous

/-- Public focused normalized replacement successor. -/
def executeFocusedNormalizedAtomReplacement
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (previous : Previous) :
    FocusedNormalizedAtomReplacementStage focus context profile :=
  (executeFocusedNormalizedAtomReplacementCounted focus context profile
    baselineInvariant targetInvariant previous).value

/-- Query the normalized replacement contradiction from the newest focused
extension. -/
def focusedNormalizedAtomReplacementQuery
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
    (profile : NormalizedAtomReplacementProfile Baseline) :
    Core.Residual.Focus.ActiveQuery
      (Core.Residual.ProofProjection.Profile focus
        (FocusedNormalizedAtomReplacementClaim focus context profile))
      (fun stage active =>
        FocusedNormalizedAtomReplacementClaim focus context profile
          stage.previous active) :=
  Core.Residual.ProofProjection.latestClaim focus
    (FocusedNormalizedAtomReplacementClaim focus context profile)

/-! ## Hereditary uncompressibility after replacement -/

/-- The registered context-universality statement over the active residual.
It is the graph-generic shape produced by the context-universality node and
consumed by hereditary uncompressibility. -/
abbrev FocusedRegisteredContextUniversalityClaim
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
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active)))
    (stage : Previous) (active : focus.Active stage) : Prop :=
  let ctx := context.read stage active
  let registered := registration.read stage active
  forall (atom : ProperBoundariedAtom ctx.G)
    (system : AtomResponse.CoordinateSystem.{u, w}
      (registered.family atom) Target)
    (quotient : AtomResponse.TargetCompleteQuotient.{u, w} system)
    {left right : system.Coordinate},
      quotient.Identified left right -> system.ContextEquivalent left right

/-- Graph-owned projection from a registered atom-response quotient to
context universality.  The registration is only read through the active
ledger query; no atom profile is copied into the successor payload. -/
def focusedRegisteredContextUniversalityProjectionQuery
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
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active))) :
    Core.Residual.Focus.ActiveQuery focus
      (FocusedRegisteredContextUniversalityClaim focus context
        registration) :=
  registration.map fun _stage _active _registered =>
    fun _atom _system quotient {_left _right} identified =>
      quotient.contextUniversal_of_identified identified

/-- Hereditary target-uncompressibility and target-defective identification,
packaged over the active residual selected by a focus. -/
abbrev FocusedNormalizedAtomUncompressibilityClaim
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active)))
    (stage : Previous) (active : focus.Active stage) : Prop :=
  let ctx := context.read stage active
  let registered := registration.read stage active
  (forall (atom : NormalizedProperBoundariedAtom ctx.G)
    (replacement : BoundaryPiece atom.toAtom.decomposition.interface),
      NormalizedAtomReplacementCertificate profile ctx atom replacement ->
        False) ∧
  forall (atom : ProperBoundariedAtom ctx.G)
    (system : AtomResponse.CoordinateSystem.{u, w}
      (registered.family atom) Target)
    {left right : system.Coordinate},
      Not (system.ContextEquivalent left right) ->
        Not (AtomResponse.TargetCompleteIdentification system left right) ∧
          AtomResponse.TargetDefect system left right

/-- Graph-owned projection from replacement plus context universality to the
hereditary uncompressibility corollary. -/
def focusedNormalizedAtomUncompressibilityProjectionQuery
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active)))
    (replacement : Core.Residual.Focus.ActiveQuery focus
      (FocusedNormalizedAtomReplacementClaim focus context profile))
    (universality : Core.Residual.Focus.ActiveQuery focus
      (FocusedRegisteredContextUniversalityClaim focus context registration)) :
    Core.Residual.Focus.ActiveQuery focus
      (FocusedNormalizedAtomUncompressibilityClaim focus context profile
        registration) :=
  (replacement.and universality).map
    fun _stage _active inherited =>
      ⟨inherited.fst,
        fun _atom _system {_left _right} notEquivalent =>
          ⟨by
              intro identified
              obtain ⟨quotient, quotientIdentifies⟩ := identified
              exact notEquivalent
                (inherited.snd _atom _system quotient quotientIdentifies),
            AtomResponse.targetDefect_of_not_contextEquivalent
              notEquivalent⟩⟩

/-- Exact accumulated successor carrying the hereditary uncompressibility
corollary. -/
abbrev FocusedNormalizedAtomUncompressibilityStage
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active))) :=
  Core.Residual.ProofProjection.Stage focus
    (FocusedNormalizedAtomUncompressibilityClaim.{u, v, w, uPrevious}
      focus context profile registration)

/-- Counted focused hereditary-uncompressibility execution. Core owns active
and inactive branch routing; Graph owns the corollary projection. -/
def executeFocusedNormalizedAtomUncompressibilityCounted
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active)))
    (replacement : Core.Residual.Focus.ActiveQuery focus
      (FocusedNormalizedAtomReplacementClaim focus context profile))
    (universality : Core.Residual.Focus.ActiveQuery focus
      (FocusedRegisteredContextUniversalityClaim focus context registration))
    (previous : Previous) :
    Core.Counted
      (FocusedNormalizedAtomUncompressibilityStage.{u, v, w, uPrevious}
        focus context profile registration) :=
  Core.Residual.ProofProjection.executeCounted focus
    (FocusedNormalizedAtomUncompressibilityClaim focus context profile
      registration)
    (focusedNormalizedAtomUncompressibilityProjectionQuery focus context
      profile registration replacement universality)
    previous

/-- Public focused hereditary-uncompressibility successor. -/
def executeFocusedNormalizedAtomUncompressibility
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active)))
    (replacement : Core.Residual.Focus.ActiveQuery focus
      (FocusedNormalizedAtomReplacementClaim focus context profile))
    (universality : Core.Residual.Focus.ActiveQuery focus
      (FocusedRegisteredContextUniversalityClaim focus context registration))
    (previous : Previous) :
    FocusedNormalizedAtomUncompressibilityStage.{u, v, w, uPrevious}
      focus context profile registration :=
  (executeFocusedNormalizedAtomUncompressibilityCounted focus context profile
    registration replacement universality previous).value

/-- Query hereditary uncompressibility from the newest focused extension. -/
def focusedNormalizedAtomUncompressibilityQuery
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active))) :
    Core.Residual.Focus.ActiveQuery
      (Core.Residual.ProofProjection.Profile focus
        (FocusedNormalizedAtomUncompressibilityClaim focus context profile
          registration))
      (fun stage active =>
        FocusedNormalizedAtomUncompressibilityClaim focus context profile
          registration stage.previous active) :=
  Core.Residual.ProofProjection.latestClaim focus
    (FocusedNormalizedAtomUncompressibilityClaim focus context profile
      registration)

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

theorem executeFocusedAtomReplacementCounted_work_within
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
    (Core.Residual.ProofProjection.workBudget focus).Within previous
      (executeFocusedAtomReplacementCounted focus context targetInvariant
        previous).checks :=
  Core.Residual.ProofProjection.executeCounted_work_within focus
    (FocusedAtomReplacementClaim focus context)
    (focusedAtomReplacementProjectionQuery focus context targetInvariant)
    previous

@[simp] theorem executeFocusedNormalizedAtomReplacementCounted_checks
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (previous : Previous) :
    (executeFocusedNormalizedAtomReplacementCounted focus context profile
      baselineInvariant targetInvariant previous).checks =
        focus.selectionBudget.checks previous := by
  change
    (Core.Residual.ProofProjection.executeCounted focus
      (FocusedNormalizedAtomReplacementClaim focus context profile)
      (focusedNormalizedAtomReplacementProjectionQuery focus context profile
        baselineInvariant targetInvariant)
      previous).checks = focus.selectionBudget.checks previous
  rw [Core.Residual.ProofProjection.executeCounted_checks]

theorem executeFocusedNormalizedAtomReplacementCounted_checks_bounded
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (previous : Previous) :
    (executeFocusedNormalizedAtomReplacementCounted focus context profile
      baselineInvariant targetInvariant previous).checks <=
        (Core.Residual.ProofProjection.workBudget focus).coefficient *
          ((Core.Residual.ProofProjection.workBudget focus).size previous + 1) ^
            (Core.Residual.ProofProjection.workBudget focus).degree :=
  Core.Residual.ProofProjection.executeCounted_checks_bounded focus
    (FocusedNormalizedAtomReplacementClaim focus context profile)
    (focusedNormalizedAtomReplacementProjectionQuery focus context profile
      baselineInvariant targetInvariant)
    previous

theorem executeFocusedNormalizedAtomReplacementCounted_work_within
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (previous : Previous) :
    (Core.Residual.ProofProjection.workBudget focus).Within previous
      (executeFocusedNormalizedAtomReplacementCounted focus context profile
        baselineInvariant targetInvariant previous).checks :=
  Core.Residual.ProofProjection.executeCounted_work_within focus
    (FocusedNormalizedAtomReplacementClaim focus context profile)
    (focusedNormalizedAtomReplacementProjectionQuery focus context profile
      baselineInvariant targetInvariant)
    previous

@[simp] theorem executeFocusedNormalizedAtomUncompressibilityCounted_checks
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active)))
    (replacement : Core.Residual.Focus.ActiveQuery focus
      (FocusedNormalizedAtomReplacementClaim focus context profile))
    (universality : Core.Residual.Focus.ActiveQuery focus
      (FocusedRegisteredContextUniversalityClaim focus context registration))
    (previous : Previous) :
    (executeFocusedNormalizedAtomUncompressibilityCounted focus context
      profile registration replacement universality previous).checks =
        focus.selectionBudget.checks previous := by
  change
    (Core.Residual.ProofProjection.executeCounted focus
      (FocusedNormalizedAtomUncompressibilityClaim focus context profile
        registration)
      (focusedNormalizedAtomUncompressibilityProjectionQuery focus context
        profile registration replacement universality)
      previous).checks = focus.selectionBudget.checks previous
  rw [Core.Residual.ProofProjection.executeCounted_checks]

theorem executeFocusedNormalizedAtomUncompressibilityCounted_checks_bounded
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active)))
    (replacement : Core.Residual.Focus.ActiveQuery focus
      (FocusedNormalizedAtomReplacementClaim focus context profile))
    (universality : Core.Residual.Focus.ActiveQuery focus
      (FocusedRegisteredContextUniversalityClaim focus context registration))
    (previous : Previous) :
    (executeFocusedNormalizedAtomUncompressibilityCounted focus context
      profile registration replacement universality previous).checks <=
        (Core.Residual.ProofProjection.workBudget focus).coefficient *
          ((Core.Residual.ProofProjection.workBudget focus).size previous + 1) ^
            (Core.Residual.ProofProjection.workBudget focus).degree :=
  Core.Residual.ProofProjection.executeCounted_checks_bounded focus
    (FocusedNormalizedAtomUncompressibilityClaim focus context profile
      registration)
    (focusedNormalizedAtomUncompressibilityProjectionQuery focus context
      profile registration replacement universality)
    previous

theorem executeFocusedNormalizedAtomUncompressibilityCounted_work_within
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
    (profile : NormalizedAtomReplacementProfile Baseline)
    (registration : Core.Residual.Focus.ActiveQuery focus
      (fun stage active =>
        BoundariedAtomRegistration (context.read stage active)))
    (replacement : Core.Residual.Focus.ActiveQuery focus
      (FocusedNormalizedAtomReplacementClaim focus context profile))
    (universality : Core.Residual.Focus.ActiveQuery focus
      (FocusedRegisteredContextUniversalityClaim focus context registration))
    (previous : Previous) :
    (Core.Residual.ProofProjection.workBudget focus).Within previous
      (executeFocusedNormalizedAtomUncompressibilityCounted focus context
        profile registration replacement universality previous).checks :=
  Core.Residual.ProofProjection.executeCounted_work_within focus
    (FocusedNormalizedAtomUncompressibilityClaim focus context profile
      registration)
    (focusedNormalizedAtomUncompressibilityProjectionQuery focus context
      profile registration replacement universality)
    previous

end Hypostructure.Graph
