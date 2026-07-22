import Hypostructure.Core.Closure
import Hypostructure.Core.Execution
import Hypostructure.Core.Provision
import Hypostructure.Core.Residual.Focus
import Hypostructure.Core.Residual.Query

/-!
# Proof-relevant declaration metadata

Metadata is authored next to compiled Lean declarations.  It records source
references and carries the actual work-bound and ledger-query objects; it does
not claim to discover declarations by inspecting source text at runtime.
-/

namespace Hypostructure.Core.Metadata

universe uPrevious uQuery uWork

/-- One actual typed query used by an executable declaration. -/
structure LedgerQueryUse (Previous : Type uPrevious) where
  source : DeclarationRef
  Result : Previous -> Type uQuery
  query : Residual.Query Previous Result

/-- One actual proof-indexed query used on a framework-owned focused branch. -/
structure FocusedLedgerQueryUse (Previous : Type uPrevious) where
  source : DeclarationRef
  profile : Residual.Focus.Profile Previous
  Result : (previous : Previous) -> profile.Active previous -> Type uQuery
  query : Residual.Focus.ActiveQuery profile Result

/-- A remaining manual obligation is a source-labelled proposition.  Complete
metadata cannot contain one. -/
structure ManualObligation where
  source : DeclarationRef
  Claim : Prop

/-- Canonical metadata for one executable declaration. -/
structure DeclarationMetadata (Previous : Type uPrevious)
    (WorkInput : Type uWork) where
  declaration : DeclarationRef
  primitiveInputs : List AuthorPrimitiveRef
  inferredDependencies : List InferredDependencyRef
  ledgerQueries : List (LedgerQueryUse.{uPrevious, uQuery} Previous)
  focusedLedgerQueries :
    List (FocusedLedgerQueryUse.{uPrevious, uQuery} Previous) := []
  frameworkSearch : List DeclarationRef
  generatedOutputs : List FrameworkOutputRef
  genericTheorems : List DeclarationRef
  closureMechanisms : List Closure.Mechanism := []
  workBound : PolynomialCheckBudget WorkInput
  manualObligations : List ManualObligation

/-- Proof that metadata is complete.  Completion is impossible while even one
manual obligation remains in the canonical list. -/
structure Complete {Previous : Type uPrevious} {WorkInput : Type uWork}
    (metadata : DeclarationMetadata Previous WorkInput) : Prop where
  manualObligations_empty : metadata.manualObligations = []

namespace Complete

/-- A complete record has no member in its manual-obligation list. -/
theorem no_manual_obligation
    {Previous : Type uPrevious} {WorkInput : Type uWork}
    {metadata : DeclarationMetadata Previous WorkInput}
    (complete : Complete metadata) (obligation : ManualObligation) :
    Not (obligation ∈ metadata.manualObligations) := by
  rw [complete.manualObligations_empty]
  exact List.not_mem_nil

/-- The work theorem stored in complete metadata remains the actual proof
carried by its polynomial budget. -/
theorem work_bounded
    {Previous : Type uPrevious} {WorkInput : Type uWork}
    {metadata : DeclarationMetadata Previous WorkInput}
    (_complete : Complete metadata) (input : WorkInput) :
    metadata.workBound.checks input <=
      metadata.workBound.coefficient *
        (metadata.workBound.size input + 1) ^ metadata.workBound.degree :=
  metadata.workBound.bounded input

end Complete

end Hypostructure.Core.Metadata
