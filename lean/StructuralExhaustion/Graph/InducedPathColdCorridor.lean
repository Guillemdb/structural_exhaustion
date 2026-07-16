import StructuralExhaustion.Core.FiniteFirstFailure
import StructuralExhaustion.Graph.InducedPathColdLedger
import StructuralExhaustion.Graph.EdgeRootedReturn
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.InducedPathColdCorridor

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathColdLedger
open scoped Sym2

universe u

variable {V : Type u}

/-!
# Graph-owned cold return corridors

This is the producer layer missing between the ambient-cubic stub ledger and
the application-level cold-germ classifier.  A corridor is not supplied by a
caller: it is the canonical deleted-edge return obtained from the already
proved non-bridge fact for one literal external incidence.  Its stages are the
vertices of that one simple return path, in path order.

The quiet output is deliberately only a `ColdStructuralGerm`.  It records a
bounded local-signature repeat (or a short terminal return), but does not
pretend to own a smaller replacement or a theorem about all outside target
contexts.  Those are later classification outputs.
-/

/-- One literal external incidence rooted in an ambient-cubic selected
`P13` window. -/
structure CubicStub (object : FiniteObject V) where
  token : Token object
  cubic : AmbientCubic object token.1

namespace CubicStub

variable {object : FiniteObject V}

abbrev window (stub : CubicStub object) : WindowIndex object := stub.token.1
abbrev position (stub : CubicStub object) : Fin 13 := stub.token.2.1
abbrev neighbor (stub : CubicStub object) : V := stub.token.2.2.1

theorem adjacent (stub : CubicStub object) :
    object.graph.Adj
      (selectedWindow object stub.window stub.position) stub.neighbor := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  have member := stub.token.2.2.2
  simp only [externalNeighbors, Finset.mem_sdiff] at member
  have ambient : stub.neighbor ∈
      ambientNeighbors object stub.window stub.position := member.1
  rw [ambientNeighbors, SimpleGraph.mem_neighborFinset] at ambient
  exact ambient

/-- The actual oriented edge represented by the incidence token. -/
noncomputable def dart (stub : CubicStub object) : object.graph.Dart :=
  ⟨(selectedWindow object stub.window stub.position, stub.neighbor),
    stub.adjacent⟩

end CubicStub

/-- Exact constructor data already proved by the earlier bridge-reduction
stage.  It is a theorem about every dart, not a corridor or outcome seed. -/
structure Producer (object : FiniteObject V) where
  notBridge : ∀ dart : object.graph.Dart, ¬object.graph.IsBridge dart.edge

namespace Producer

variable {object : FiniteObject V}

/-- Canonical simple return after deleting the selected external stub. -/
noncomputable def returnPath (producer : Producer object)
    (stub : CubicStub object) :
    DartReturn object.graph stub.dart :=
  DartReturn.ofNotBridge (producer.notBridge stub.dart)

/-- Ambient view of the canonical deleted-edge return. -/
noncomputable def ambientReturn (producer : Producer object)
    (stub : CubicStub object) :
    object.graph.Walk stub.neighbor
      (selectedWindow object stub.window stub.position) :=
  (producer.returnPath stub).path.mapLe
    (object.graph.deleteEdges_le {stub.dart.edge})

theorem ambientReturn_isPath (producer : Producer object)
    (stub : CubicStub object) :
    (producer.ambientReturn stub).IsPath :=
  (producer.returnPath stub).isPath.mapLe _

/-- The concrete stage order scanned by node 153. -/
noncomputable def stages (producer : Producer object)
    (stub : CubicStub object) : Core.OrderedCollection V where
  values := (producer.ambientReturn stub).support
  nodup := producer.ambientReturn_isPath stub |>.support_nodup
  decEq := object.input.vertices.decEq

/-- Restore the root stub to obtain the literal simple cycle carried by this
return. -/
noncomputable def rootCycle (producer : Producer object)
    (stub : CubicStub object) : object.graph.Walk
      (selectedWindow object stub.window stub.position)
      (selectedWindow object stub.window stub.position) :=
  .cons stub.adjacent (producer.ambientReturn stub)

theorem rootCycle_isCycle (producer : Producer object)
    (stub : CubicStub object) : (producer.rootCycle stub).IsCycle := by
  let unrestricted := (producer.returnPath stub).toEdgeRootedReturn
  exact unrestricted.cycle_isCycle

theorem rootCycle_length (producer : Producer object)
    (stub : CubicStub object) :
    (producer.rootCycle stub).length =
      (producer.ambientReturn stub).length + 1 := by
  simp [rootCycle, ambientReturn]

/-- Exact target hit discovered at the final stage of a return corridor. -/
structure TargetHit (producer : Producer object) (LengthOK : Nat → Prop) where
  stub : CubicStub object
  cycle : CycleWithLength object.graph LengthOK

/-- Exact surplus handoff discovered at the first high-degree corridor
vertex.  Under a minimum-degree-three baseline, `high` means that this vertex
pays a positive surplus unit. -/
structure SurplusHandoff (producer : Producer object) where
  stub : CubicStub object
  vertex : V
  high : 3 < object.degree vertex

/-- Honest F5 output of the graph producer.  It contains only facts actually
derived from the corridor scan.  Its support bound is the exact finite ambient
bound, not the manuscript's currently unjustified constant `Q_cold`.  In
particular it has no `locallySmaller`, target-response repeat, or
`contextCoverage` field. -/
structure ColdStructuralGerm (producer : Producer object)
    (LengthOK : Nat → Prop) (stub : CubicStub object) where
  marker : Unit := ()
  supportBound : (producer.ambientReturn stub).support.length ≤
    object.input.vertices.card
  rootLengthRejected : ¬LengthOK (producer.rootCycle stub).length
  allSubcubic : ∀ vertex ∈ (producer.stages stub).values,
    ¬3 < object.degree vertex

/-- Computed promotion boundary for a concrete scale.  A short corridor may
be handed to a genuinely finite target-relative classifier.  A long corridor
is retained as an explicit residual for scale arithmetic (for example CT17);
it is never relabelled as a bounded germ. -/
inductive ScaleDecision (producer : Producer object)
    (LengthOK : Nat → Prop) (stub : CubicStub object)
    (germ : ColdStructuralGerm producer LengthOK stub) (scale : Nat) where
  | short
      (bounded : (producer.ambientReturn stub).support.length ≤ scale)
  | long
      (exceeds : scale < (producer.ambientReturn stub).support.length)

/-- Exact, outcome-free scale classifier. -/
noncomputable def classifyScale (producer : Producer object) (LengthOK : Nat → Prop)
    (stub : CubicStub object)
    (germ : ColdStructuralGerm producer LengthOK stub) (scale : Nat) :
    ScaleDecision producer LengthOK stub germ scale := by
  by_cases bounded : (producer.ambientReturn stub).support.length ≤ scale
  · exact .short bounded
  · exact .long (Nat.lt_of_not_ge bounded)

theorem classifyScale_exhaustive (producer : Producer object)
    (LengthOK : Nat → Prop) (stub : CubicStub object)
    (germ : ColdStructuralGerm producer LengthOK stub) (scale : Nat) :
    (∃ bounded, producer.classifyScale LengthOK stub germ scale =
      .short bounded) ∨
    (∃ exceeds, producer.classifyScale LengthOK stub germ scale =
      .long exceeds) := by
  cases equation : producer.classifyScale LengthOK stub germ scale with
  | short bounded => exact Or.inl ⟨bounded, rfl⟩
  | long exceeds => exact Or.inr ⟨exceeds, rfl⟩

end Producer

/-! ## CT6-style priority scan via `FiniteFirstFailure` -/

section FirstFailure

variable {object : FiniteObject V}
variable (producer : Producer object)
variable (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)

noncomputable def F1 (stub : CubicStub object) (vertex : V) : Prop :=
  vertex = selectedWindow object stub.window stub.position ∧
    LengthOK (producer.rootCycle stub).length

def F4 (_stub : CubicStub object) (vertex : V) : Prop :=
  3 < object.degree vertex

noncomputable def targetHitOfF1 (stub : CubicStub object) (vertex : V)
    (hit : F1 producer LengthOK stub vertex) :
    Producer.TargetHit producer LengthOK where
  stub := stub
  cycle := {
    vertex := selectedWindow object stub.window stub.position
    walk := producer.rootCycle stub
    isCycle := producer.rootCycle_isCycle stub
    length_ok := hit.2
  }

def surplusHandoffOfF4 (stub : CubicStub object) (vertex : V)
    (high : F4 stub vertex) :
    Producer.SurplusHandoff producer where
  stub := stub
  vertex := vertex
  high := high

/-- The exact finite first-failure machine.  F2 and F3 are intentionally
empty here: target-context distinction and smaller-replacement construction
belong to the subsequent promotion/classification layer. -/
noncomputable def firstFailureProfile :
    Core.FiniteFirstFailure.Profile (CubicStub object) V where
  corridors := by
    letI : FinEnum (Token object) := tokens object
    letI : DecidablePred (fun token : Token object =>
        AmbientCubic object token.1) := fun token =>
      ambientCubicDecidable object token.1
    let accepted := Core.Enumeration.subtype (tokens object)
      (fun token => AmbientCubic object token.1)
      (fun token => ambientCubicDecidable object token.1)
    letI := accepted
    exact FinEnum.ofEquiv
      {token : Token object // AmbientCubic object token.1}
      { toFun := fun stub => ⟨stub.token, stub.cubic⟩
        invFun := fun token => ⟨token.1, token.2⟩
        left_inv := by intro stub; cases stub; rfl
        right_inv := by intro token; cases token; rfl }
  stages := producer.stages
  F1 := F1 producer LengthOK
  F2 := fun _ _ => False
  F3 := fun _ _ => False
  F4 := F4
  f1Decidable := fun stub vertex =>
    @instDecidableAnd _ _ (object.input.vertices.decEq vertex
      (selectedWindow object stub.window stub.position))
      (lengthOKDecidable (producer.rootCycle stub).length)
  f2Decidable := fun _ _ => isFalse id
  f3Decidable := fun _ _ => isFalse id
  f4Decidable := fun _ vertex => by
    unfold F4
    infer_instance
  F1Data := Producer.TargetHit producer LengthOK
  F2Data := Empty
  F3Data := Empty
  F4Data := Producer.SurplusHandoff producer
  f1Data := targetHitOfF1 producer LengthOK
  f2Data := fun _ _ impossible => impossible.elim
  f3Data := fun _ _ impossible => impossible.elim
  f4Data := fun stub vertex high => {
    stub := stub
    vertex := vertex
    high := high
  }
  Germ := fun stub => Producer.ColdStructuralGerm producer LengthOK stub
  germOfClear := fun stub clear => {
    marker := ()
    supportBound := by
      letI : FinEnum V := object.input.vertices
      simpa [FinEnum.card_eq_fintypeCard] using
        (producer.ambientReturn_isPath stub).support_nodup.length_le_card
    rootLengthRejected := by
      intro accepted
      have finalMem : selectedWindow object stub.window stub.position ∈
          (producer.stages stub).values := by
        change selectedWindow object stub.window stub.position ∈
          (producer.ambientReturn stub).support
        simpa only [SimpleGraph.Walk.getVert_length] using
          ((producer.ambientReturn stub).getVert_mem_support
            (producer.ambientReturn stub).length)
      have noF1 := (clear _ finalMem).1
      apply noF1
      exact ⟨rfl, accepted⟩
    allSubcubic := by
      intro vertex member high
      exact (clear vertex member).2.2.2 high
  }

abbrev FirstFailureResult (stub : CubicStub object) :=
  (firstFailureProfile producer LengthOK lengthOKDecidable).Result stub

/-- Execute node 153 from one actual cubic external stub. -/
noncomputable def runFirstFailure (stub : CubicStub object) :
    FirstFailureResult producer LengthOK lengthOKDecidable stub :=
  (firstFailureProfile producer LengthOK lengthOKDecidable).run stub

theorem runFirstFailure_total (stub : CubicStub object) :
    (∃ hit data, runFirstFailure producer LengthOK lengthOKDecidable stub =
      .first hit data) ∨
    (∃ noEvent germ,
      runFirstFailure producer LengthOK lengthOKDecidable stub =
        .germ noEvent germ) :=
  (firstFailureProfile producer LengthOK lengthOKDecidable).run_total stub

end FirstFailure

end StructuralExhaustion.Graph.InducedPathColdCorridor
