import StructuralExhaustion.Graph.FanClosedPairAssembly

namespace StructuralExhaustion.Examples.FanClosedPairAssembly

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u}
variable {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : FiniteObject V} {baseline : base.problem.Baseline object}
variable {center : V} (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
variable (profile : FanClosedPort.FanWindowProfile V)
variable (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
variable (pair : FanClosedPort.CompatiblePair centerHigh deletionCritical first second)

/-- Non-Erdős transfer of the whole assembly into the constant-work CT5
stage. -/
example
    (firstClosed : FanClosedPort.FanClosed centerHigh deletionCritical profile first)
    (secondClosed : FanClosedPort.FanClosed centerHigh deletionCritical profile second) :
    Graph.FanClosedPairAssembly.Assembly (base := base) (baseline := baseline)
      centerHigh deletionCritical profile first second pair firstClosed secondClosed :=
  Graph.FanClosedPairAssembly.assemble (base := base) (baseline := baseline)
    centerHigh deletionCritical profile first second pair firstClosed secondClosed

end StructuralExhaustion.Examples.FanClosedPairAssembly
