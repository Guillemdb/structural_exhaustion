import StructuralExhaustion.Graph.FanClosedPort

namespace StructuralExhaustion.Graph.FanClosedPairAssembly

open StructuralExhaustion

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

/-- Assemble the exact four assignment proofs from two graph-derived closed
ports. -/
def assignedPair
    (firstClosed : FanClosedPort.FanClosed centerHigh deletionCritical profile first)
    (secondClosed : FanClosedPort.FanClosed centerHigh deletionCritical profile second) :
    FanClosedPort.AssignedPair centerHigh deletionCritical profile first second where
  firstRemainder := firstClosed.1
  secondRemainder := secondClosed.1
  firstAssigned := firstClosed.2
  secondAssigned := secondClosed.2

structure Assembly
    (firstClosed : FanClosedPort.FanClosed centerHigh deletionCritical profile first)
    (secondClosed : FanClosedPort.FanClosed centerHigh deletionCritical profile second) :
    Prop where
  assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile first second
  stage : FanClosedPort.VerifiedStage (base := base) (baseline := baseline)
    centerHigh deletionCritical profile first second pair assigned

/-- Generic CT5 transfer from two closed ports and one compatible-pair proof. -/
noncomputable def assemble
    (firstClosed : FanClosedPort.FanClosed centerHigh deletionCritical profile first)
    (secondClosed : FanClosedPort.FanClosed centerHigh deletionCritical profile second) :
    Assembly (base := base) (baseline := baseline) centerHigh deletionCritical
      profile first second pair firstClosed secondClosed := by
  let assigned := assignedPair centerHigh deletionCritical profile first second
    firstClosed secondClosed
  exact {
    assigned := assigned
    stage := FanClosedPort.verifiedStage (base := base) (baseline := baseline)
      centerHigh deletionCritical profile first second pair assigned }

end StructuralExhaustion.Graph.FanClosedPairAssembly
