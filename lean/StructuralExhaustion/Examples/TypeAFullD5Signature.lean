import StructuralExhaustion.Graph.TypeAFullD5Signature

namespace StructuralExhaustion.Examples.TypeAFullD5Signature

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : TypeACanonicalReceiverTrace.SupportProfile object)

/-- Transfer fixture: the graph-level D5 label really identifies its exact
coordinate, independently of the Erdős carrier. -/
example : Function.Injective
    (Graph.TypeAFullD5Signature.BaseCoordinate.label object profile) :=
  Graph.TypeAFullD5Signature.BaseCoordinate.label_injective object profile

/-- Transfer fixture: the complete kind/label/support/value datum is likewise
injective before any problem-specific finite coding. -/
example (producer : Graph.TypeAFullD5Signature.ReturnProducer object profile) :
    Function.Injective
      (Graph.TypeAFullD5Signature.exactDatum object profile producer) :=
  Graph.TypeAFullD5Signature.exactDatum_injective object profile producer

/-- Transfer fixture: the source-by-position bound is graph-generic and scans
only a supplied carrier of size at most thirty. -/
example (carrier : Finset V)
    (carrierVertices : FinEnum (Graph.TypeAFullD5Signature.CarrierVertex carrier))
    (carrierBound : carrier.card ≤ 30) :
    (Graph.TypeAFullD5Signature.localTraceIncidencesFromCarrier object profile
      carrier carrierVertices).card ≤ 900 :=
  Graph.TypeAFullD5Signature.localTraceIncidencesFromCarrier_card_le_900
    object profile carrier carrierVertices carrierBound

/-- Transfer fixture: every base label supported on the carrier is present in
the filtered schedule. -/
example (producer : Graph.TypeAFullD5Signature.ReturnProducer object profile)
    (carrier : Finset V)
    (carrierVertices : FinEnum (Graph.TypeAFullD5Signature.CarrierVertex carrier))
    (coordinate : Graph.TypeAFullD5Signature.BaseCoordinate object profile)
    (supported : Graph.TypeAFullD5Signature.declaredSupport object profile producer
      coordinate ⊆ carrier) :
    (⟨coordinate, supported⟩ :
      Graph.TypeAFullD5Signature.LocalBaseCoordinate object profile producer carrier) ∈
      (Graph.TypeAFullD5Signature.localBaseCoordinatesFromCarrier
        object profile producer carrier carrierVertices).orderedValues :=
  Graph.TypeAFullD5Signature.localBaseCoordinate_mem_fromCarrier
    object profile producer carrier carrierVertices ⟨coordinate, supported⟩

/-- The same carrier-first schedule has a graph-independent fixed envelope on
any 28-role carrier; no ambient profile coordinate list is inspected. -/
example (carrier : Finset V) (carrierBound : carrier.card ≤ 28) :
    Graph.TypeAFullD5Signature.carrierVisibleChecks carrier ≤ 5516 :=
  Graph.TypeAFullD5Signature.carrierVisibleChecks_le_5516 carrier carrierBound

/-- The generic layer exposes the precise later producer, not a fabricated
theta or carrier coordinate. -/
example (producer : Graph.TypeAFullD5Signature.ReturnProducer object profile)
    (carrier : Finset V) :
    (Graph.TypeAFullD5Signature.pending object profile producer carrier
      .crossPortThetaConstraint).origin =
        .saturatedReceiverClassifier := rfl

end StructuralExhaustion.Examples.TypeAFullD5Signature
