import StructuralExhaustion.Graph.DegreeFourFanLedger

namespace StructuralExhaustion.Examples.DegreeFourFanLedger

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u uAmbient uBranch

variable {V : Type u} (object : FiniteObject V) (center : V)
variable (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
variable (Assigned : FanClosedPort.LocalCarrier V → Prop)
variable (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
variable {P : Core.Problem.{uAmbient, uBranch}} (context : Core.BranchContext P)
variable (degreeFour : object.degree center = 4)

/-- Non-Erdős transfer of the exact actual-port CT14 ledger. -/
example : Graph.DegreeFourFanLedger.VerifiedStage object center centerHigh
    deletionCritical Assigned assignedDecidable context degreeFour :=
  Graph.DegreeFourFanLedger.verifiedStage object center centerHigh
    deletionCritical Assigned assignedDecidable context degreeFour

example : Graph.DegreeFourFanLedger.checks object center ≤
    17 * (object.input.vertices.card + 1) :=
  (Graph.DegreeFourFanLedger.verifiedStage object center centerHigh
    deletionCritical Assigned assignedDecidable context degreeFour).polynomial

end StructuralExhaustion.Examples.DegreeFourFanLedger
