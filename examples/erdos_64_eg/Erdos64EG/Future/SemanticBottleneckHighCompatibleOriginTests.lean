import Erdos64EG.Future.SemanticBottleneckHighCompatibleOrigin

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable {V : Type u} {object : Graph.FiniteObject V} {center : V}
variable {centerHigh : 4 ≤ object.degree center}
variable {deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3}
variable {first second : Graph.HighCenterPort.Port object center}

/-! Regression test for the exact high-compatible boundary.  The assigned
profile is consumed, not reconstructed from degree or compatibility. -/
example
    {frontier : Graph.HighCompatiblePortOrigin.AssignmentFrontier object center
      centerHigh deletionCritical first second}
    (entry : Graph.HighCompatiblePortOrigin.AssignedEntry object center
      centerHigh deletionCritical frontier) :
    Graph.FanClosedPort.FanClosed centerHigh deletionCritical entry.profile
        frontier.origin.firstPort ∧
      Graph.FanClosedPort.FanClosed centerHigh deletionCritical entry.profile
        frontier.origin.secondPort :=
  assignedOpenPair_fanClosed entry

#print axioms assignedOpenPair_fanClosed

end Erdos64EG.Internal
