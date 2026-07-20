import Erdos64EG.Future.PendingNodes.Node53

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [54]: entropy-cap terminal

The original diagram has two incoming edges.  On `[52] -> [54]`, the exact
joint feasibility inequality excludes its strict reverse.  On the yes edge of
node [53], the strict small-budget comparison contradicts the corresponding
independent-capacity certificate.  The latter old certificate is temporarily
accepted through one exactly indexed typed-yellow input while its producer is
migrated; no sibling branch can consume it.
-/

/-- Exact strict reverse of node [52]'s finite joint feasibility inequality. -/
def Node54HighTheta {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) : Prop :=
  node22SkeletonRateNumerator *
      (Node21Context active.previous).G.object.input.vertices.card <
    node24HighEntropyRemainderNumerator *
        ((Node21Context active.previous).G.object.input.vertices.card -
          13 * node22PackingCount active.previous) +
      node22WindowRateNumerator * node22PackingCount active.previous

/-- Node [54]'s new terminal fact on the literal node-[52] leaf. -/
structure Node54HighOutput {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual)
    (_high : Node50High residual active)
    (_node52 : Node52Output active _high) : Type (u + 2) where
  highThetaImpossible : ¬ Node54HighTheta active

noncomputable def node54HighOutput {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual)
    (high : Node50High residual active) (node52 : Node52Output active high) :
    Node54HighOutput active high node52 :=
  ⟨not_lt_of_ge node52.jointBudget⟩

/-- The branch-local capacity statement used by the paper on node [53]'s
strict small-budget edge. -/
abbrev Node54SmallCapacity {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual)
    (_low : Node50Low residual active) : Prop :=
  node53ForcedCurvatureBits active ≤
    node53RemainingNoncurvatureBits active

/-- Temporary exact reuse of the old independent-capacity output.  Its
indices include the literal node-[50] low and node-[53] small proofs, so it
cannot leak to the large-budget sibling. -/
structure Node54SmallCapacityTypedYellowInput (V : Type u) : Type (u + 3) where
  capacity : ∀ {residual : InitialResidual V}
    (active : Node50Active V residual)
    (low : Node50Low residual active)
    (small : Node53Small residual active low),
      Node54SmallCapacity active low

theorem node54SmallBudgetImpossible {V : Type u}
    {residual : InitialResidual V} {active : Node50Active V residual}
    {low : Node50Low residual active}
    (small : Node53Small residual active low)
    (capacity : Node54SmallCapacity active low) : False :=
  (not_lt_of_ge capacity) small

/-- Core-owned bypass after node [54]: either an earlier Part-IV bypass or
the terminal certificate on the exact node-[52] high leaf. -/
abbrev Node54Bypass (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchYesTerminalBypass
    (Node50Bypass V) (Node50Active V)
    (@Node50High V)
    (fun residual active high =>
      Node52Output (residual := residual) active high)
    (fun _residual active high node52 =>
      Node54HighOutput active high node52)

/-- The sole surviving Part-IV leaf after node [54]. -/
abbrev Node54Active (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchNestedNoActive
    (Node50Active V) (@Node50Low V) (@Node53Large V)

abbrev Node54Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranch
    (Node54Bypass V) (Node54Active V) residual

/-- Terminalize the node-[52] high edge, close only node [53]'s small edge,
and focus its complementary large-budget leaf. -/
noncomputable def node54P13EntropyCapClosure {V : Type u}
    (input : Node54SmallCapacityTypedYellowInput V) {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node53Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node54Stage V) :=
  Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes
      (fun _residual active high node52 =>
        node54HighOutput active high node52)
      (fun _residual active low small =>
        node54SmallBudgetImpossible small
          (input.capacity active low small))

noncomputable def runInitialThroughNode54 {V : Type u}
    (quietBlock : Node23DenseWindowQuietBlockInput V)
    (node48Input : Node48TypedYellowInput V)
    (node52Input : Node52JointAccountingTypedYellowInput V)
    (node54Input : Node54SmallCapacityTypedYellowInput V)
    (residual : InitialResidual V) :=
  (runInitialThroughNode53 quietBlock node48Input
    node52Input residual).mapYesStage
      (node54P13EntropyCapClosure node54Input)

/-- Node [54] performs only proof-level inequality elimination. -/
def node54LocalChecks : Nat := 0

theorem node54LocalChecks_eq_zero : node54LocalChecks = 0 := rfl

#print axioms node54HighOutput
#print axioms node54SmallBudgetImpossible
#print axioms node54P13EntropyCapClosure
#print axioms runInitialThroughNode54

end Erdos64EG.Internal
