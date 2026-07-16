import Erdos64EG.P13ActualAttachmentResponse
import Erdos64EG.P13SequentialEntropyFiltration
import StructuralExhaustion.Routes.SequentialRatioFailureHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# P13 sequential-ratio reflection audit

The graph-owned response interface currently available at one selected P13
window has thirteen literal adjacency coordinates.  Node [21] separately has
ninety-one audited finite compatibility barriers.  The equalities below pin
that interface mismatch without supplying a caller-authored identification.

Consequently an arithmetic `SequentialRatioFailureHandoff.Residual` is not a
CT6/CT7/CT10 residual.  A semantic route would first need a graph theorem
constructing ninety-one executable completion predicates and proving their
agreement with the node-[21] safe/flat relations on the exact retained
before/after fibres.  Neither `P13ActualAttachmentResponse` nor node [21]
contains that reflection theorem.
-/

/-- The literal graph-owned attachment interface has thirteen coordinates. -/
theorem p13ActualAttachment_coordinate_count
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx) :
    (p13ActualAttachmentSystem ctx window).coordinates.card = 13 :=
  p13ActualAttachmentSystem_coordinateCard ctx window

/-- The independently audited node-[21] barrier table has ninety-one rows. -/
theorem p13Sequential_barrier_count :
    p13BarrierClassification.classCount = 91 :=
  p13Barrier_class_count

/-- The existing graph-owned coordinate interface is strictly smaller than
the barrier table; no definitional coordinate identification is available. -/
theorem p13ActualAttachment_coordinates_lt_barriers
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : InducedP13Window ctx) :
    (p13ActualAttachmentSystem ctx window).coordinates.card <
      p13BarrierClassification.classCount := by
  rw [p13ActualAttachment_coordinate_count ctx window,
    p13Sequential_barrier_count]
  decide

end Erdos64EG.Internal
