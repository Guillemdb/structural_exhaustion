import StructuralExhaustion.CT3.Theorems
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace StructuralExhaustion.CT3

/-- Literal packed-graph replacement profile.  Its required data are local;
the derived operations prove gluing arithmetic, whole-rank decrease, baseline
preservation, and target transport before entering the CT3 reduction kernel. -/
def literalPackedReplacementCapabilityProfile : Core.CapabilityProfile where
  capabilityId :=
    "StructuralExhaustion.CT3.profile.literalPackedReplacement"
  tacticId := "CT3"
  requiredDefinitions := [
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.glue",
      .userOperator⟩,
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.Context.noBoundaryEdge",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.reconstruct",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.connected",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.proper",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.boundaryDegree_eq",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.obstructionIncluded",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.internalTargetFree",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.internalBaseline",
      .instanceBridge⟩,
    ⟨"StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.locallySmaller",
      .instanceBridge⟩
  ]
  requiredInstances := [
    "StructuralExhaustion.Graph.PackedBoundariedGluing.Context.noBoundaryEdge",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.reconstruct",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.connected",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.proper",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.boundaryDegree_eq",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.obstructionIncluded",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.internalTargetFree",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.internalBaseline",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.locallySmaller"
  ]
  derivedOperations := [
    "StructuralExhaustion.Graph.PackedBoundariedGluing.glue_vertexCount",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.glue_edgeCount",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.glue_lexRank_lt",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.glue_preserves_minDegree",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.minDegree_iff_of_iso",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.lexRank_eq_of_iso",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.hasCycleWithLength_iff_of_iso",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.certifiedInput",
    "StructuralExhaustion.CT3.runCertifiedCompression",
    "StructuralExhaustion.CT3.runCertifiedCompression_terminal",
    "StructuralExhaustion.CT3.runCertifiedCompression_trace",
    "StructuralExhaustion.CT3.runCertifiedCompression_total",
    "StructuralExhaustion.CT3.certifiedCompressionBudget",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.impossible",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_polynomial",
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage"
  ]

/-- Complete transition-facing contracts for CT3's semantic residuals. -/
def residualKindContracts : List Core.ResidualKindContract := [
  {
    residualKindId := "CT3.residual.distinguishingContext"
    leanType := "StructuralExhaustion.CT3.DistinguishingContextResidual S C input"
    semanticFields := [
      ⟨"row", "S.Row", .derivedByGenericSearch⟩,
      ⟨"rowMember", "row ∈ C.rows.orderedValues", .derivedByGenericTheorem⟩,
      ⟨"context", "S.Context", .derivedByGenericSearch⟩,
      ⟨"contextMember", "context ∈ C.contexts.orderedValues", .derivedByGenericTheorem⟩,
      ⟨"differs", "S.response (S.rowPiece row) context ≠ S.rowResponse row context",
        .derivedByGenericSearch⟩
    ]
    inheritedContext := .branch
  },
  {
    residualKindId := "CT3.residual.novelExternalType"
    leanType := "StructuralExhaustion.CT3.NovelExternalTypeResidual S C input table"
    semanticFields := [
      ⟨"novel", "∀ row, ¬ CT3.RowMatches S input row",
        .derivedByGenericTheorem⟩
    ]
    inheritedContext := .branch
  }
]

def residualKindIds : List String :=
  residualKindContracts.map fun contract => contract.residualKindId

/-- Aggregate node-level provenance inventory. -/
def nodeAutomationContracts : List Core.NodeAutomationContract := [
  Nodes.Entry.automationContract,
  Nodes.Vector.automationContract,
  Nodes.Compression.automationContract,
  Nodes.TableValidation.automationContract,
  Nodes.Lookup.automationContract
]

/-- Execute CT3 from its source input and finite capability. -/
syntax (name := ct3Execute) "ct3_execute " term " using " term : term

macro_rules
  | `(ct3_execute $input:term using $capability:term) =>
      `(StructuralExhaustion.CT3.run _ $capability $input)

/-- Discharge the structural soundness statement of a concrete CT3 run. -/
syntax (name := ct3Tactic) "ct3 " term " using " term : tactic

macro_rules
  | `(tactic| ct3 $input:term using $capability:term) =>
      `(tactic| exact StructuralExhaustion.CT3.run_verified
        _ $capability $input)

/-- Discharge totality and typed-trace validity. -/
syntax (name := ct3TotalTactic) "ct3_total " term " using " term : tactic

macro_rules
  | `(tactic| ct3_total $input:term using $capability:term) =>
      `(tactic| exact StructuralExhaustion.CT3.run_total
        _ $capability $input)

end StructuralExhaustion.CT3
