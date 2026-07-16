import StructuralExhaustion.Graph.InducedPathComponentD4D7Evaluation
import StructuralExhaustion.Graph.TypeATraceIncidenceCoordinate

namespace StructuralExhaustion.Graph.InducedPathComponentD5Availability

open StructuralExhaustion

universe u

/-!
# Same-support D5 availability and missing-input residual

A positive D5 branch must own a genuine Type A support profile whose support
is exactly the active support of the retained component marker.  Such a
profile proves connectivity, ambient cubicity, the internal degree bound, and
internal 3-core freeness.  Only then may the canonical trace-incidence
schedule be exposed.

The current component predecessor does not provide that profile.  Its honest
execution therefore supplies `none` and returns the typed missing-input
residual below.  The classifier accepts `some ownership` only as a future
proof-carrying graph producer output; it never constructs D5 from D4, D7, or a
density hypothesis.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (componentInput :
  InducedPathComponentBoundarySchedule.Input ctx.G.object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

namespace Previous
export InducedPathComponentD4D7Evaluation (Evaluation)
end Previous

/-- Proof-carrying ownership required to interpret clause D5 on this exact
component support. -/
structure Ownership where
  profile : TypeACanonicalReceiverTrace.SupportProfile ctx.G.object
  supportExact : profile.support = InducedPathComponentD4.activeSupport componentInput

namespace Ownership

variable (ownership : Ownership componentInput)

abbrev Coordinate :=
  TypeATraceIncidenceCoordinate.Coordinate ctx.G.object ownership.profile

@[implicit_reducible]
noncomputable def coordinates : FinEnum ownership.Coordinate :=
  TypeATraceIncidenceCoordinate.coordinates ctx.G.object ownership.profile

theorem coordinate_support_subset_active (coordinate : ownership.Coordinate) :
    coordinate.support ctx.G.object ownership.profile ⊆
      InducedPathComponentD4.activeSupport componentInput := by
  intro vertex member
  have singleton : vertex = coordinate.ambientVertex ctx.G.object ownership.profile := by
    simpa [TypeATraceIncidenceCoordinate.Coordinate.support] using member
  subst vertex
  rw [← ownership.supportExact]
  exact coordinate.ambientVertex_mem_profile ctx.G.object ownership.profile

theorem coordinates_quadratic :
    (ownership.coordinates componentInput).card ≤
      ctx.G.object.input.vertices.card *
        (ctx.G.object.input.vertices.card + 1) :=
  (TypeATraceIncidenceCoordinate.coordinates_card_le_visibleChecks
      ctx.G.object ownership.profile).trans
    (TypeATraceIncidenceCoordinate.visibleChecks_polynomial
      ctx.G.object ownership.profile)

end Ownership

/-- The exact graph facts absent from the current predecessor. -/
inductive MissingInput
  | exactTypeASupportProfile
  | sameActiveSupportProof
  | connectedSupportProof
  | ambientCubicProof
  | internalDegreeBoundProof
  | internalCoreFreeProof
  deriving DecidableEq, Repr

def missingInputs : List MissingInput :=
  [.exactTypeASupportProfile, .sameActiveSupportProof, .connectedSupportProof,
    .ambientCubicProof, .internalDegreeBoundProof, .internalCoreFreeProof]

theorem missingInputs_nodup : missingInputs.Nodup := by decide

/-- Positive result.  D5 is an actual dependent trace schedule; D6 and the
Boolean semantics for D7 remain unresolved. -/
structure Available
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : Previous.Evaluation stage componentInput LengthOK
      lengthOKDecidable d4) where
  predecessor : Previous.Evaluation stage componentInput LengthOK
    lengthOKDecidable d4
  predecessorExact : predecessor = previous
  ownership : Ownership componentInput
  coordinates : FinEnum ownership.Coordinate
  coordinatesExact : coordinates = ownership.coordinates componentInput
  pending : List InducedPathComponentD4D7ClauseSchedule.ClauseSlot
  pendingExact : pending = [.d6, .d7]

/-- Honest negative execution result when the predecessor supplies no exact
same-support Type A profile.  It retains the full D4/D7 output. -/
structure Missing
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : Previous.Evaluation stage componentInput LengthOK
      lengthOKDecidable d4) where
  predecessor : Previous.Evaluation stage componentInput LengthOK
    lengthOKDecidable d4
  predecessorExact : predecessor = previous
  required : List MissingInput
  requiredExact : required = missingInputs
  requiredNodup : required.Nodup
  pending : List InducedPathComponentD4D7ClauseSchedule.ClauseSlot
  pendingExact : pending = [.d5, .d6, .d7]

inductive Result
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : Previous.Evaluation stage componentInput LengthOK
      lengthOKDecidable d4) where
  | available (output : Available stage componentInput LengthOK
      lengthOKDecidable previous)
  | missing (residual : Missing stage componentInput LengthOK
      lengthOKDecidable previous)

/-- Classify a proof-carrying output from a graph-owned ownership producer.
`none` means precisely that no such predecessor output is present. -/
noncomputable def classify
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : Previous.Evaluation stage componentInput LengthOK
      lengthOKDecidable d4)
    (candidate : Option (Ownership componentInput)) :
    Result stage componentInput LengthOK lengthOKDecidable previous :=
  match candidate with
  | some ownership => .available {
      predecessor := previous
      predecessorExact := rfl
      ownership := ownership
      coordinates := ownership.coordinates componentInput
      coordinatesExact := rfl
      pending := [.d6, .d7]
      pendingExact := rfl
    }
  | none => .missing {
      predecessor := previous
      predecessorExact := rfl
      required := missingInputs
      requiredExact := rfl
      requiredNodup := missingInputs_nodup
      pending := [.d5, .d6, .d7]
      pendingExact := rfl
    }

/-- Current dependency-ready execution: node 194 plus D7 supplies no Type A
profile, so D5 remains a typed missing input rather than a fabricated empty
coordinate family. -/
noncomputable def runCurrent
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : Previous.Evaluation stage componentInput LengthOK
      lengthOKDecidable d4) :
    Result stage componentInput LengthOK lengthOKDecidable previous :=
  classify stage componentInput LengthOK lengthOKDecidable previous none

theorem runCurrent_is_missing
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : Previous.Evaluation stage componentInput LengthOK
      lengthOKDecidable d4) :
    ∃ residual, runCurrent stage componentInput LengthOK lengthOKDecidable
      previous = .missing residual :=
  ⟨_, rfl⟩

end StructuralExhaustion.Graph.InducedPathComponentD5Availability
