import StructuralExhaustion.Graph.HighOpenEndpointFailure

namespace StructuralExhaustion.Examples.HighOpenEndpointFailure

open StructuralExhaustion Graph

universe u

/-! A theorem-generic, non-Erdős transfer test for the four-case local split. -/

variable {V : Type u} {object : FiniteObject V} {center : V}
variable {centerHigh : 4 ≤ object.degree center}
variable {deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3}
variable {first second : HighCenterPort.Port object center}

noncomputable example
    (failure : HighSeparatorPortClassification.OpenEndpointFailure object center
      centerHigh deletionCritical first second) :
    Graph.HighOpenEndpointFailure.NormalizedFailure object center centerHigh
      deletionCritical first second :=
  Graph.HighOpenEndpointFailure.classify object center centerHigh
    deletionCritical failure

noncomputable example
    (failure : HighSeparatorPortClassification.OpenEndpointFailure object center
      centerHigh deletionCritical first second) :
    let normalized := Graph.HighOpenEndpointFailure.classify object center
      centerHigh deletionCritical failure
    object.graph.Adj
      (HighCenterPort.endpoint object center normalized.foreign)
      (HighCenterPort.endpoint object center normalized.suppressed) := by
  dsimp
  exact (Graph.HighOpenEndpointFailure.classify object center centerHigh
    deletionCritical failure).endpoints_adjacent

noncomputable example
    (failure : HighSeparatorPortClassification.OpenEndpointFailure object center
      centerHigh deletionCritical first second) :
    let normalized := Graph.HighOpenEndpointFailure.classify object center
      centerHigh deletionCritical failure
    OpenPortSuppression.Setup object :=
  let normalized := Graph.HighOpenEndpointFailure.classify object center
    centerHigh deletionCritical failure
  Graph.HighOpenEndpointFailure.suppressionSetup object center centerHigh
    deletionCritical normalized.suppressed normalized.suppressedOpen

end StructuralExhaustion.Examples.HighOpenEndpointFailure
