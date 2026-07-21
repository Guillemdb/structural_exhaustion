import Erdos64EG.Node158
import StructuralExhaustion.CT3.Automation

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor
open StructuralExhaustion.Graph.InducedPathColdGermScale

universe u

/-!
# Diagram node [159]: CT3 check on bounded G3 same-interface residuals

Node [159] consumes the exact node-[158] bounded same-interface residual and
executes the framework CT3 runner on each scheduled bounded germ.  The local
Erdos-specific payload is only the finite response instantiation: source and
candidate pieces are path lengths, coordinates are finite return lengths, and
the response bit is the power-of-two cycle-length test.  CT3 owns the vector
computation, compression search, table validation, row lookup, terminal
evidence, typed trace, totality, and work bound.
-/

noncomputable abbrev node159SourceLength {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) : Nat :=
  ((node153CorridorProducer active.data.data).ambientReturn entry).length

abbrev Node159Coordinate {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual) :=
  Fin (Node158Scale active + 1)

abbrev Node159Candidate {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :=
  {length :
      Fin (((node153CorridorProducer active.data.data).ambientReturn entry).support.length) //
    0 < length.1 ∧ length.1 < node159SourceLength active entry}

@[implicit_reducible]
noncomputable def node159Coordinates {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual) :
    FinEnum (Node159Coordinate active) :=
  inferInstance

@[implicit_reducible]
noncomputable def node159Candidates {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    FinEnum (Node159Candidate active entry) :=
  Core.Enumeration.subtype
    (inferInstance :
      FinEnum
        (Fin (((node153CorridorProducer active.data.data).ambientReturn entry).support.length)))
    (fun length => 0 < length.1 ∧ length.1 < node159SourceLength active entry)
    (fun _ => inferInstance)

def node159Response {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual) (pieceLength : Nat)
    (returnLength : Node159Coordinate active) : Bool :=
  decide (PowerOfTwoLength (pieceLength + returnLength.1))

abbrev Node159AdmissibleReplacement {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object)
    (_object : PackedProblem.{u}.Ambient) (_source : Nat)
    (candidate : Node159Candidate active entry) : Prop :=
  0 < candidate.1.1

abbrev Node159StrictlySmaller {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object)
    (_object : PackedProblem.{u}.Ambient) (source : Nat)
    (candidate : Node159Candidate active entry) : Prop :=
  candidate.1.1 < source

noncomputable abbrev node159Spec {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    CT3.Spec PackedProblem.{u} where
  Piece := Nat
  Context := Node159Coordinate active
  Candidate := Node159Candidate active entry
  Row := Node159Candidate active entry
  response := node159Response active
  candidatePiece := fun candidate => candidate.1.1
  Admissible := Node159AdmissibleReplacement active entry
  Smaller := Node159StrictlySmaller active entry
  rowPiece := fun row => row.1.1
  rowResponse := fun row => node159Response active row.1.1

private theorem node159_candidateCard_le_scale {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    (node159Candidates active entry).card ≤ Node158Scale active := by
  calc
    (node159Candidates active entry).card ≤
        ((node153CorridorProducer active.data.data).ambientReturn
          entry).support.length := by
      simpa [FinEnum.card_eq_fintypeCard] using
        Core.Enumeration.subtype_card_le
          (inferInstance :
            FinEnum
              (Fin (((node153CorridorProducer active.data.data).ambientReturn
                entry).support.length)))
          (fun length =>
            0 < length.1 ∧ length.1 < node159SourceLength active entry)
          (fun _ => inferInstance)
    _ ≤ Node158Scale active := by
      simpa [Node158Scale, FinEnum.orderedValues_length] using
        Core.Enumeration.length_le_elems_of_nodup
          (Node21Context active.data.data.node18).G.object.input.vertices
          ((node153CorridorProducer active.data.data).ambientReturn_isPath
            entry).support_nodup

private theorem node159WorkBound {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    CT3.localCheckBound (node159Coordinates active)
      (node159Candidates active entry) (node159Candidates active entry) ≤
        8 * (Node158Scale active + 1) ^ 2 := by
  have candidateBound := node159_candidateCard_le_scale active entry
  simp only [CT3.localCheckBound, FinEnum.orderedValues_length]
  simp only [FinEnum.card_eq_fintypeCard, Fintype.card_fin] at *
  nlinarith

noncomputable def node159Capability {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    CT3.Capability (node159Spec active entry) where
  contexts := node159Coordinates active
  candidates := node159Candidates active entry
  rows := node159Candidates active entry
  admissibleDecidable := fun _object _source candidate =>
    inferInstanceAs (Decidable (0 < candidate.1.1))
  smallerDecidable := fun _object source candidate =>
    inferInstanceAs (Decidable (candidate.1.1 < source))
  inputSize := fun _object => Node158Scale active
  workCoefficient := 8
  workDegree := 2
  workBound := by
    intro _object
    exact node159WorkBound active entry

noncomputable def node159Input {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    CT3.Input (node159Spec active entry) where
  context := (Node21Context active.data.data.node18).toBranchContext
  piece := node159SourceLength active entry

def node159RowCandidateEmbedding {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    CT3.RowCandidateEmbedding (node159Spec active entry)
      (node159Input active entry) where
  rowCandidate := fun row => row
  rowCandidatePiece := fun _row => rfl
  rowAdmissible := fun row => row.2.1
  rowSmaller := fun row => row.2.2
  rowResponse_exact := fun _row _context => rfl

noncomputable def node159Run {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :=
  CT3.run (node159Spec active entry) (node159Capability active entry)
    (node159Input active entry)

abbrev Node159BudgetClaim {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    Prop :=
  CT3.localCheckBound (node159Coordinates active)
      (node159Candidates active entry) (node159Candidates active entry) ≤
    8 * (Node158Scale active + 1) ^ 2

abbrev Node159CT3Output {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (_g3 : Node156G3Silent active) : Prop :=
    ∀ entry ∈ node152BranchExcessSchedule active.data.data,
      ∃ noEvent, ∃ germ,
        InducedPathColdCorridor.runFirstFailure
            (node153CorridorProducer active.data.data) PowerOfTwoLength
            powerOfTwoLengthDecidable entry = .germ noEvent germ ∧
        ∃ bounded :
          BoundedSameInterfaceResidual
            (node153CorridorProducer active.data.data) PowerOfTwoLength
            entry germ (Node158Scale active),
          InducedPathColdGermScale.route
            (node153CorridorProducer active.data.data) PowerOfTwoLength
            entry germ (Node158Scale active) = .short bounded ∧
          CT3.OutcomeClaim (node159Run active entry).outcome ∧
          @CT3.Graph.ValidTrace PackedProblem.{u}
            (node159Spec active entry) (node159Capability active entry)
            (node159Input active entry) (node159Run active entry).trace ∧
          Node159BudgetClaim active entry

abbrev Node159Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
      (Node154Bypass V) (Node154LiveLeaf V)
      (@Node154G1Hit V) (@Node154NoG1 V))
    (Node156Active V) (@Node156G2Event V) (@Node156G3Silent V)
    (@Node159CT3Output V) residual

noncomputable def node159CT3Refinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node158Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node159Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := fun _residual active g3 =>
      Node158BoundedSameInterfaceOutput active g3)
    (Next := fun _residual active g3 =>
      Node159CT3Output active g3)
    fun _residual active _g3 node158 => by
      intro entry member
      rcases node158 entry member with
        ⟨noEvent, germ, hrun, bounded, hroute⟩
      exact
        ⟨noEvent, germ, hrun, bounded, hroute,
          CT3.run_verified (node159Spec active entry)
            (node159Capability active entry) (node159Input active entry),
          CT3.run_trace_valid (node159Spec active entry)
            (node159Capability active entry) (node159Input active entry),
          node159WorkBound active entry⟩

noncomputable def runInitialThroughNode159 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode158 residual).mapYesStage
    node159CT3Refinement

noncomputable def node159LocalChecks {V : Type u} {residual : InitialResidual V}
    (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    Nat :=
  CT3.localCheckBound (node159Coordinates active)
    (node159Candidates active entry) (node159Candidates active entry)

theorem node159LocalChecks_polynomial {V : Type u}
    {residual : InitialResidual V} (active : Node156Active V residual)
    (entry : CubicStub (Node21Context active.data.data.node18).G.object) :
    node159LocalChecks active entry ≤ 8 * (Node158Scale active + 1) ^ 2 :=
  node159WorkBound active entry

#print axioms node159CT3Refinement
#print axioms runInitialThroughNode159

end Erdos64EG.Internal
