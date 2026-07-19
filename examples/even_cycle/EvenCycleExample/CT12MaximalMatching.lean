import EvenCycleExample.Concrete
import EvenCycleExample.CT1InducedEdge
import StructuralExhaustion.Graph.MaximumMatching
import StructuralExhaustion.Routes.CT1ToCT12

namespace EvenCycleExample.MaximalMatching

open StructuralExhaustion

/-!
# External maximum-matching CT12 fixture

The reusable graph layer owns maximum matching selection, the selected-list
CT12 audit, the unmatched partition, and remainder edgelessness.  This file
only pins the execution on `K₄`.
-/

namespace ConcreteK4

open EvenCycleExample.ConcreteK4

def ct1Source : Routes.CT1ToCT12.PackedC1
    (Graph.InducedPath.edgeProfile Vertex).encoding.spec
    (Graph.InducedPath.edgeInput object) :=
  ⟨(), Graph.InducedPath.edgeCertificate object InducedEdge.ConcreteK4.dart,
    trivial⟩

def currentC1
    (previous : CT1.CertifiedC1Run
      (Graph.InducedPath.edgeProfile Vertex).encoding.spec
      (Graph.InducedPath.edgeInput object)) :
    Routes.CT1ToCT12.PackedC1
      (Graph.InducedPath.edgeProfile Vertex).encoding.spec
      (Graph.InducedPath.edgeInput object) := by
  rcases previous with ⟨result, checks, terminal, trace, checksEq⟩
  cases result with
  | mk terminalId path outcome =>
      cases outcome with
      | c1 certificate => exact certificate.target
      | avoiding state => cases terminal

abbrev ct1Ledger : Core.Routing.ResidualStage .ct1
    (CT1.CertifiedC1Run
      (Graph.InducedPath.edgeProfile Vertex).encoding.spec
      (Graph.InducedPath.edgeInput object)) :=
  Core.Routing.ResidualStage.exact InducedEdge.ConcreteK4.execution

noncomputable def routeAdapter : Routes.CT1ToCT12.SemanticAdapter
    (S := (Graph.InducedPath.edgeProfile Vertex).encoding.spec)
    (input := Graph.InducedPath.edgeInput object)
    (CT12.ListPeeling.capability (Graph.FiniteObject.problem Vertex)
      (Graph.MaximumMatching.Edge object)) where
  trigger := fun _source => {
    load := (Graph.MaximumMatching.profile object).values.length
    state := CT12.ListPeeling.initialState
      (Graph.MaximumMatching.profile object).values
  }
  Evidence := fun _source _trigger => Graph.MaximumMatching.edges object ≠ []
  evidence := by
    intro source
    rcases source with ⟨_unit, certificate, _accepts⟩
    exact Graph.InducedPathPacking.windows_nonempty_of_realization object 2
      (by decide) ⟨certificate⟩

noncomputable def routedTransition := Routes.CT1ToCT12.transition
  (CT12.ListPeeling.capability (Graph.FiniteObject.problem Vertex)
    (Graph.MaximumMatching.Edge object)) routeAdapter

noncomputable def routedStage := Routes.CT1ToCT12.advance
  (CT12.ListPeeling.capability (Graph.FiniteObject.problem Vertex)
    (Graph.MaximumMatching.Edge object)) routeAdapter currentC1 ct1Ledger

noncomputable def routedLedger := routedStage.ledgerStage

theorem transition_profile_id :
    routedTransition.profileId = Routes.CT1ToCT12.transitionId := rfl

theorem routed_matching_nonempty : Graph.MaximumMatching.edges object ≠ [] :=
  Routes.CT1ToCT12.evidence_preserved _ routeAdapter currentC1 ct1Ledger

noncomputable def execution :=
  Graph.MaximumMatching.run object (Graph.FiniteObject.context object)

theorem routed_execution_exact : routedStage.targetResult = execution := rfl

theorem exhausted : execution.terminal = .exhausted :=
  Graph.MaximumMatching.run_terminal_exhausted object
    (Graph.FiniteObject.context object)

theorem bounded : execution.iterations ≤ object.input.vertices.card :=
  Graph.MaximumMatching.run_iterations_le_vertices object
    (Graph.FiniteObject.context object)

/-- Transfer check for the generic complement-floor bookkeeping used by the
Erdős remainder residual. -/
theorem unmatched_floor_of_matching_ceiling (ceiling : Nat)
    (packingBound : Graph.MaximumMatching.matchingNumber object ≤ ceiling) :
    object.input.vertices.card - 2 * ceiling ≤
      (Graph.MaximumMatching.remainderVertices object).card :=
  Graph.InducedPathPacking.remainder_card_ge_of_packingNumber_le
    object 2 (by decide) ceiling packingBound

end ConcreteK4

end EvenCycleExample.MaximalMatching
