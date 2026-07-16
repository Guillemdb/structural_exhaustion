import EvenCycleExample.Concrete
import StructuralExhaustion.Graph.TwoRoleFanMass

namespace EvenCycleExample.CT14TwoRoleFanMass

open StructuralExhaustion

/-!
Graph-semantic transfer on the concrete `K₄` used by the textbook theorem
that minimum degree three forces an even cycle.  Each actual vertex supplies
its literal degree-above-two unit in each of two bookkeeping roles.  One
grouped occurrence is extracted; CT14 scans all eight role--center entries,
with the extracted entry contributing zero and the other seven retaining mass.
-/

abbrev Center := ConcreteK4.Vertex

def centerSurplus (center : Center) : Nat :=
  ConcreteK4.object.degree center - 2

def active (_role : Graph.TwoRoleFanMass.Role) (_center : Center) : Prop := True

def extracted : Graph.TwoRoleFanMass.Role → Center → Prop
  | .grouped, .v0 => True
  | _, _ => False

def deficit (_role : Graph.TwoRoleFanMass.Role) (_center : Center) : Nat := 1

def profile : Graph.TwoRoleFanMass.Profile Center where
  centers := ConcreteK4.vertices
  centerSurplus := centerSurplus
  active := active
  activeDecidable := fun role center => by
    unfold active
    exact inferInstance
  deficit := deficit
  extracted := extracted
  extractedDecidable := fun role center => by
    cases role <;> cases center <;> simp [extracted] <;> infer_instance
  coefficient := 3
  localBound := by
    intro role center _active _notExtracted
    cases role <;> cases center <;> native_decide

def context : Core.BranchContext ConcreteK4.surplusBase.problem :=
  Graph.FanClosedPortMass.context ConcreteK4.surplusBase ConcreteK4.object
    ConcreteK4.minimumDegreeThree

def stage : profile.VerifiedStage context :=
  profile.verifiedStage context

theorem terminal : (profile.run context).terminal = .capacity :=
  stage.terminal

theorem trace : (profile.run context).trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal] :=
  stage.trace

theorem semantic_mass : profile.residualMass = 7 := by native_decide

theorem two_role_bound : profile.residualMass ≤ 24 := by
  have mass := stage.massBound
  have surplusEq : profile.globalSurplus = 4 := by native_decide
  rw [surplusEq] at mass
  exact mass

theorem total : ∃ result : CT14.ExecutionResult
    (profile.capability ConcreteK4.surplusBase.problem) context,
    result.outcome.Valid ∧ @CT14.Graph.ValidTrace
      ConcreteK4.surplusBase.problem
      (profile.capability ConcreteK4.surplusBase.problem) context result.trace :=
  stage.total

theorem linearWork : profile.checks ≤
    9 * (profile.centers.card + 1) :=
  stage.polynomial

end EvenCycleExample.CT14TwoRoleFanMass
