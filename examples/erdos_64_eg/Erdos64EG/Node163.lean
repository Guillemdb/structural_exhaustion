import Erdos64EG.Node161
import StructuralExhaustion.Graph.FiniteSameInterfaceExchange

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor
open StructuralExhaustion.Graph.FiniteSameInterfaceExchange

universe u

/-!
# Diagram node [163]: CT3 good-terminal replacement extraction

Node [163] consumes the yes side of node [161].  It extracts the common
framework fact supplied by both
CT3 good terminals: a predecessor-owned candidate length that is positive,
strictly shorter than the source, has the same finite response vector, and
therefore supplies the framework same-interface target-completeness ledger for
that exact finite response table.
-/

noncomputable def node163Representatives {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (entry : CubicStub (Node21Context active.data.data.data.node18).G.object)
    (candidate : Node159Candidate active.data entry) :
    FiniteSameInterfaceExchange.Representatives Nat :=
  FiniteSameInterfaceExchange.Representatives.exact
    (node159SourceLength active.data entry) candidate.1.1 (fun length => length)

def node163BoundaryCompatible {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (entry : CubicStub (Node21Context active.data.data.data.node18).G.object)
    (candidate : Node159Candidate active.data entry) :
    FiniteSameInterfaceExchange.BoundaryCompatible
      (node163Representatives active entry candidate) where
  Profile := Unit
  profile := fun _ => ()
  equal := rfl

noncomputable def node163ResponseTable {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (entry : CubicStub (Node21Context active.data.data.data.node18).G.object)
    (candidate : Node159Candidate active.data entry) :
    FiniteSameInterfaceExchange.ResponseTable
      (node163Representatives active entry candidate) where
  Outside := Node159Coordinate active.data
  Code := Node159Coordinate active.data
  codes := node159Coordinates active.data
  decode := id
  targetResponseReplacement := fun context =>
    node159Response active.data candidate.1.1 context = true
  targetResponseSource := fun context =>
    node159Response active.data (node159SourceLength active.data entry)
      context = true
  replacementResponse := fun code =>
    node159Response active.data candidate.1.1 code
  sourceResponse := fun code =>
    node159Response active.data (node159SourceLength active.data entry) code
  replacementReflect := by
    intro code
    rfl
  sourceReflect := by
    intro code
    rfl
  coverage := by
    intro outside
    exact ⟨outside, Iff.rfl, Iff.rfl⟩

theorem node163FiniteTargetComplete {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (entry : CubicStub (Node21Context active.data.data.data.node18).G.object)
    (candidate : Node159Candidate active.data entry)
    (sameResponse :
      CT3.SameResponse (node159Spec active.data entry)
        candidate.1.1 (node159SourceLength active.data entry)) :
    FiniteSameInterfaceExchange.TargetComplete
      (node163Representatives active entry candidate)
      (node163BoundaryCompatible active entry candidate)
      (node163ResponseTable active entry candidate) := by
  constructor
  · rfl
  · intro outside
    have responseEq :
        node159Response active.data candidate.1.1 outside =
          node159Response active.data (node159SourceLength active.data entry)
            outside := by
      simpa [node159Spec] using sameResponse outside
    change
      (node159Response active.data candidate.1.1 outside = true) ↔
        (node159Response active.data (node159SourceLength active.data entry)
          outside = true)
    constructor
    · intro replacementTrue
      rwa [responseEq] at replacementTrue
    · intro sourceTrue
      rwa [responseEq]

abbrev Node163StrictResponseReplacementOutput {V : Type u}
    {residual : InitialResidual V} (active : Node160Active V residual)
    (_allGood : Node160AllCompressionOrKnown active) : Prop :=
    ∀ entry ∈ node152BranchExcessSchedule active.data.data.data,
      ∃ candidate : Node159Candidate active.data entry,
        0 < candidate.1.1 ∧
          candidate.1.1 < node159SourceLength active.data entry ∧
          CT3.SameResponse (node159Spec active.data entry)
            candidate.1.1 (node159SourceLength active.data entry) ∧
          FiniteSameInterfaceExchange.TargetComplete
            (node163Representatives active entry candidate)
            (node163BoundaryCompatible active entry candidate)
            (node163ResponseTable active entry candidate)

abbrev Node163Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node160Bypass V) (Node160Active V)
    (@Node160AllCompressionOrKnown V) (@Node160HasCT3Residual V)
    (@Node163StrictResponseReplacementOutput V) residual

noncomputable def node163StrictResponseReplacementContinuation {V : Type u}
    {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node161Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node163Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    (Output := @Node161CompressionStyleOutput V)
    (Next := @Node163StrictResponseReplacementOutput V)
    fun _residual active _allGood node161 => by
      intro entry member
      rcases node161 entry member with
        ⟨candidate, compresses⟩ | ⟨row, rowMatches⟩
      · let replacement :=
          CT3.strictResponseReplacement_of_compresses
            (S := node159Spec active.data entry)
            (input := node159Input active.data entry) compresses
        exact
          ⟨replacement.candidate, replacement.admissible,
            replacement.smaller, replacement.sameResponse,
            node163FiniteTargetComplete active entry replacement.candidate
              replacement.sameResponse⟩
      · let replacement :=
          CT3.strictResponseReplacement_of_rowMatches
            (S := node159Spec active.data entry)
            (input := node159Input active.data entry)
            (node159RowCandidateEmbedding active.data entry) rowMatches
        exact
          ⟨replacement.candidate, replacement.admissible,
            replacement.smaller, replacement.sameResponse,
            node163FiniteTargetComplete active entry replacement.candidate
              replacement.sameResponse⟩

noncomputable def runInitialThroughNode163 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode161 residual).mapYesStage
    node163StrictResponseReplacementContinuation

def node163LocalChecks : Nat := 0

theorem node163LocalChecks_eq_zero : node163LocalChecks = 0 := rfl

#print axioms node163StrictResponseReplacementContinuation
#print axioms runInitialThroughNode163
#print axioms node163FiniteTargetComplete

end Erdos64EG.Internal
