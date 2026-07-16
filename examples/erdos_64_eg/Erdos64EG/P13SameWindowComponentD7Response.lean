import Erdos64EG.P13SameWindowComponentD4D7Support
import StructuralExhaustion.Graph.InducedPathComponentD7Response

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Same-marker component D7 context-indexed response profile

This is a thin application of the graph-owned D7 response restriction to the
exact post-node-194 support output.  It retains the predecessor literally and
adds only the existing target response as a function of a supplied outside
context.  It neither chooses nor enumerates contexts and does not discharge
the pending D7 Boolean semantics.
-/

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}
variable {input : P13SameWindowNormalizedBoundaryInput (short := short)}
variable {computed : P13SameWindowComputedNormalizedReturnBoundary input}

namespace P13SameWindowFirstTransitionBoundaryInput

variable (transition : P13SameWindowFirstTransitionBoundaryInput computed)
variable (source174 : P13SameWindowComponentD1D3LedgerSource transition)
variable (source175 : P13SameWindowComponentD4D7OrCoarseRepeatSource
  transition source174)
variable (source180 : transition.D4D7SemanticReadinessSource source174 source175)
variable (source182 : transition.D4D7ClauseScheduleSource source174 source175 source180)
variable (source185 : transition.D4D7ClauseCursorSource source174 source175
  source180 source182)
variable (source188 : transition.D4LocalClauseRequestSource source174 source175
  source180 source182 source185)
variable (source191 : transition.D4EvaluatorResidualSource source174 source175
  source180 source182 source185 source188)
variable (source194 : transition.D4EvaluatorConstructionSource source174 source175
  source180 source182 source185 source188 source191)

abbrev ExactD7ResponseProfile
    (componentInput : InducedPathComponentBoundarySchedule.Input ctx.G.object) :=
  {profile : FiniteSupportResponse.Profile packedStaticInput ctx
      (InducedPathComponentD7.Coordinate (D7Stage ctx) componentInput) //
    profile = InducedPathComponentD7Response.responseProfile
      (D7Stage ctx) componentInput}

def D7ResponseProfiles : transition.D4D7SupportOutput source174 → Type u
  | .coarse b _f _s _fc _sc _fr _sr _fx _sx _fb _sb _fe _se _fd7 _sd7 =>
      ExactD7ResponseProfile b.routed.residual.repetition.firstInput ×
        ExactD7ResponseProfile b.routed.residual.repetition.secondInput
  | .bounded b _o _oc _orq _ox _build _evaluation _d7 =>
      ExactD7ResponseProfile
        (InducedPathComponentD1D3Ledger.connectorInput
          (transition.d1d3LedgerInput source174) b.routed.residual.scan.row)

structure D7ResponseOutput where
  predecessor : transition.D4D7SupportOutput source174
  predecessorExact : predecessor = transition.runD4D7Support source174 source175
    source180 source182 source185 source188 source191 source194
  profiles : transition.D7ResponseProfiles source174 predecessor

noncomputable def runD7Response : transition.D7ResponseOutput source174 source175
    source180 source182 source185 source188 source191 source194 := by
  let predecessor := transition.runD4D7Support source174 source175 source180
    source182 source185 source188 source191 source194
  refine { predecessor := predecessor, predecessorExact := rfl, profiles := ?_ }
  cases predecessor with
  | coarse b f s fc sc fr sr fx sx fb sb fe se fd7 sd7 =>
      exact
        (⟨InducedPathComponentD7Response.responseProfile (D7Stage ctx)
            b.routed.residual.repetition.firstInput, rfl⟩,
         ⟨InducedPathComponentD7Response.responseProfile (D7Stage ctx)
            b.routed.residual.repetition.secondInput, rfl⟩)
  | bounded b o oc orq ox build evaluation d7 =>
      exact ⟨InducedPathComponentD7Response.responseProfile (D7Stage ctx)
          (InducedPathComponentD1D3Ledger.connectorInput
            (transition.d1d3LedgerInput source174) b.routed.residual.scan.row), rfl⟩

theorem runD7Response_predecessor_exact :
    (transition.runD7Response source174 source175 source180 source182 source185
      source188 source191 source194).predecessor =
        transition.runD4D7Support source174 source175 source180 source182 source185
          source188 source191 source194 :=
  (transition.runD7Response source174 source175 source180 source182 source185
    source188 source191 source194).predecessorExact

end P13SameWindowFirstTransitionBoundaryInput
end Erdos64EG.Internal
