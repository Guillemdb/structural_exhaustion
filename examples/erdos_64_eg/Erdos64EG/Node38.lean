import Erdos64EG.Node37

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [38]: at-original representative or enlarged support

On node [36]'s universal edge, the retained determination certificate has one
exhaustive framework location: its connected carrier is the original proper
atom, or it strictly enlarges that atom.  In the first case the certificate's
`originalRepresentative` is exactly the smaller proper representative printed
by the paper.  Node [38] decides only this location; nodes [39] and [40]
consume its two literal constructors.
-/

/-- The yes edge of node [38].  The representative is transported from the
certificate only after this exact equality is known. -/
abbrev Node38AtOriginal {V : Type u} {residual : InitialResidual V}
    {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    {node31 : Node31Output node18 bounded node21 low}
    {rankDrop : Node32RankDrop node18}
    (node35 : Node35Output node18 bounded node21 low node31 rankDrop) : Prop :=
  node35.certificate.carrier = node35.certificate.original

/-- The no edge of node [38]. -/
abbrev Node38Enlarged {V : Type u} {residual : InitialResidual V}
    {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    {node31 : Node31Output node18 bounded node21 low}
    {rankDrop : Node32RankDrop node18}
    (node35 : Node35Output node18 bounded node21 low node31 rankDrop) : Prop :=
  (Node35DeterminationSupportProfile node18).SupportLt
    node35.certificate.original node35.certificate.carrier

/-- Read the support-location router as the exact at-original decision. -/
noncomputable def node38AtOriginalDecidable {V : Type u}
    {residual : InitialResidual V}
    {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    {node31 : Node31Output node18 bounded node21 low}
    {rankDrop : Node32RankDrop node18}
    (node35 : Node35Output node18 bounded node21 low node31 rankDrop) :
    Decidable (Node38AtOriginal node35) := by
  cases node35.certificate.location with
  | atOriginal equal => exact isTrue equal
  | enlarged strict =>
      exact isFalse (fun equal => strict.2 equal.symm)

/-- The complementary constructor is the strict support growth already proved
by the same certificate router. -/
noncomputable def node38EnlargedOfNotAtOriginal {V : Type u}
    {residual : InitialResidual V}
    {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    {node31 : Node31Output node18 bounded node21 low}
    {rankDrop : Node32RankDrop node18}
    (node35 : Node35Output node18 bounded node21 low node31 rankDrop)
    (absent : ¬ Node38AtOriginal node35) : Node38Enlarged node35 := by
  cases node35.certificate.location with
  | atOriginal equal => exact (absent equal).elim
  | enlarged strict => exact strict

/-- Node [38]'s exhaustive framework decision on the universal node-[36]
leaf.  Node [37]'s sibling terminal is not an input to this decision. -/
abbrev Node38Stage {V : Type u} (residual : InitialResidual V) :=
  (node35FocusedFamily V).YesDecision
    (fun _ data => Node36OriginalUniversal data.output)
    (fun _ data => Node37TargetDefect data.output)
    (fun _ data _ => Node38AtOriginal data.output)
    (fun _ data _ => Node38Enlarged data.output) residual

/-- Framework-owned `[36] --yes--> [38]` decision. -/
noncomputable def node38P13ProperRepresentativeDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node36Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node38Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedYesContinuationYes
    (node35FocusedFamily V)
    (fun _ data _ => node38AtOriginalDecidable data.output)
    (fun _ data _ absent =>
      node38EnlargedOfNotAtOriginal data.output absent)

noncomputable def runInitialThroughNode38 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode37 residual).mapYesStage
    node38P13ProperRepresentativeDecision

def node38LocalChecks : Nat := 0

theorem node38LocalChecks_eq_zero : node38LocalChecks = 0 := rfl

#print axioms node38AtOriginalDecidable
#print axioms node38P13ProperRepresentativeDecision
#print axioms runInitialThroughNode38

end Erdos64EG.Internal
