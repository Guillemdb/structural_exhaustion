import StructuralExhaustion.Graph.DegreeFourFanLedger
import StructuralExhaustion.Routes.Accumulated

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

noncomputable def target :=
  ((Graph.DegreeFourFanLedger.profile object center centerHigh
    deletionCritical Assigned assignedDecidable).capability P).executableInterface

noncomputable def adapter : Routes.Accumulated.Adapter Unit
    (target object center centerHigh deletionCritical Assigned
      assignedDecidable (P := P)) where
  targetContext := fun _source => context
  trigger := fun _source => ⟨⟩

def source : Core.Routing.ResidualStage .ct9 Unit :=
  Core.Routing.ResidualStage.exact ()

noncomputable def transitionStage :=
  Routes.Accumulated.advance
    (target object center centerHigh deletionCritical Assigned
      assignedDecidable (P := P))
    (adapter object center centerHigh deletionCritical Assigned
      assignedDecidable context)
    id source

/-- Non-Erdős transfer from the literal accumulated CT14 result. -/
example : Graph.DegreeFourFanLedger.VerifiedExecutionStage object center
    centerHigh deletionCritical Assigned assignedDecidable context degreeFour
    (transitionStage object center centerHigh deletionCritical Assigned
      assignedDecidable context).targetResult :=
  Graph.DegreeFourFanLedger.verifiedExecutionStage object center centerHigh
    deletionCritical Assigned assignedDecidable context degreeFour _ rfl

example : Graph.DegreeFourFanLedger.checks object center ≤
    17 * (object.input.vertices.card + 1) :=
  (Graph.DegreeFourFanLedger.verifiedExecutionStage object center centerHigh
    deletionCritical Assigned assignedDecidable context degreeFour
    (transitionStage object center centerHigh deletionCritical Assigned
      assignedDecidable context).targetResult rfl).polynomial

end StructuralExhaustion.Examples.DegreeFourFanLedger
