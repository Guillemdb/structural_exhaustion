import StructuralExhaustion.CT3.Theorems

namespace StructuralExhaustion.CT3

/-- Complete router-facing contracts for CT3's semantic residuals. -/
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
