import Erdos64EG.Node35

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [36]: original-interface context audit

The support-stratified certificate retained at node [35] has distinct final-
carrier and original-atom context types.  Node [36] executes exactly the
framework certificate's `auditOriginal` decision.  Its yes edge is universal
at the original interface; its no edge retains one concrete response mismatch.
No context family is enumerated.
-/

/-- The literal yes predicate printed at node [36]. -/
abbrev Node36OriginalUniversal {V : Type u} {residual : InitialResidual V}
    {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    {node31 : Node31Output node18 bounded node21 low}
    {rankDrop : Node32RankDrop node18}
    (node35 : Node35Output node18 bounded node21 low node31 rankDrop) : Prop :=
  ∀ context : (Node35DeterminationSupportProfile node18).Context
      node35.certificate.original,
    (Node35DeterminationSupportProfile node18).response
        node35.certificate.original node35.certificate.basisCoordinate context =
      (Node35DeterminationSupportProfile node18).response
        node35.certificate.original node35.certificate.determined context

/-- The literal no predicate printed at node [36]. -/
abbrev Node36OriginalDefect {V : Type u} {residual : InitialResidual V}
    {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    {node31 : Node31Output node18 bounded node21 low}
    {rankDrop : Node32RankDrop node18}
    (node35 : Node35Output node18 bounded node21 low node31 rankDrop) : Prop :=
  ∃ context : (Node35DeterminationSupportProfile node18).Context
      node35.certificate.original,
    (Node35DeterminationSupportProfile node18).response
        node35.certificate.original node35.certificate.basisCoordinate context ≠
      (Node35DeterminationSupportProfile node18).response
        node35.certificate.original node35.certificate.determined context

/-- Read the certificate's proof-level original-interface audit as the exact
yes/no decision required by the paper. -/
noncomputable def node36OriginalUniversalDecidable {V : Type u}
    {residual : InitialResidual V}
    {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    {node31 : Node31Output node18 bounded node21 low}
    {rankDrop : Node32RankDrop node18}
    (node35 : Node35Output node18 bounded node21 low node31 rankDrop) :
    Decidable (Node36OriginalUniversal node35) := by
  cases node35.certificate.auditOriginal with
  | defective context mismatch =>
      exact isFalse (fun allContexts => mismatch (allContexts context))
  | universal allContexts => exact isTrue allContexts

/-- The complementary constructor is the concrete target-defect witness from
the same exhaustive audit. -/
noncomputable def node36OriginalDefectOfNotUniversal {V : Type u}
    {residual : InitialResidual V}
    {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    {node31 : Node31Output node18 bounded node21 low}
    {rankDrop : Node32RankDrop node18}
    (node35 : Node35Output node18 bounded node21 low node31 rankDrop)
    (absent : ¬ Node36OriginalUniversal node35) :
    Node36OriginalDefect node35 := by
  cases node35.certificate.auditOriginal with
  | defective context mismatch => exact ⟨context, mismatch⟩
  | universal allContexts => exact (absent allContexts).elim

/-- Core-owned family of the populated node-[35] continuation. -/
abbrev node35FocusedFamily (V : Type u) :=
  Core.ResidualRefinement.State.FocusedYesContinuationFamily.mk
    (@Node32Bypass V) (@Node32Active V)
    (fun _ data => Node32RankDrop data.previous)
    (fun _ data => Node32FullRank data.previous)
    (fun _ data rankDrop => Node35Output data.previous data.outerProof
      data.outerOutput data.innerProof data.current rankDrop)

/-- Node [36] is a nested framework decision on node [35]'s active rank-drop
payload.  The full-rank edge and the earlier bypass remain literal. -/
abbrev Node36Stage {V : Type u} (residual : InitialResidual V) :=
  (node35FocusedFamily V).Decision
    (fun _ data => Node36OriginalUniversal data.output)
    (fun _ data => Node36OriginalDefect data.output) residual

/-- Framework-owned `[35] → [36]` decision.  Erdős code supplies only the
certificate-local audit predicates. -/
noncomputable def node36P13OriginalContextAudit {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node35Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node36Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedYesContinuation
    (node35FocusedFamily V)
    (fun _ data => node36OriginalUniversalDecidable data.output)
    (fun _ data absent => node36OriginalDefectOfNotUniversal data.output absent)

noncomputable def runInitialThroughNode36 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode35 residual).mapYesStage
    node36P13OriginalContextAudit

/-- The audit is proof-level and performs no finite scan. -/
def node36LocalChecks : Nat := 0

theorem node36LocalChecks_eq_zero : node36LocalChecks = 0 := rfl

#print axioms node36OriginalUniversalDecidable
#print axioms node36P13OriginalContextAudit
#print axioms runInitialThroughNode36

end Erdos64EG.Internal
