import Erdos64EG.TypeANodes86To88Thresholds
import StructuralExhaustion.Core.WorkBudget

namespace Erdos64EG.Internal.TypeANode89SaturationDecision

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61 := TypeANode63Support.Node61 ctx
abbrev Node63 (node61 : Node61 (ctx := ctx)) :=
  TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61
abbrev Node86 {node61 : Node61 (ctx := ctx)} (node63 : Node63 node61) :=
  TypeANodes86To88Thresholds.VerifiedNode86Residual node61 node63
abbrev Node87 {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (node86 : Node86 node63) :=
  TypeANodes86To88Thresholds.VerifiedNode87Residual node86
abbrev Node88 {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} (node87 : Node87 node86) :=
  TypeANodes86To88Thresholds.VerifiedNode88Residual node87

/-- Node `[89]` uses the exact support profile carried by the Type-A branch;
no receiver family is supplied by the caller. -/
noncomputable def input
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) :
    Core.FiniteReceiverDischarge.Input node63.typeAProfile.Vertex where
  vertices := (node63.typeAProfile.supportObject ctx.G.object).input.vertices
  support := by
    letI : FinEnum node63.typeAProfile.Vertex :=
      (node63.typeAProfile.supportObject ctx.G.object).input.vertices
    exact Finset.univ
  degree := (node63.typeAProfile.supportObject ctx.G.object).degree
  degree_le_three := fun vertex _member =>
    node63.typeAProfile.degree_le_three vertex

/-- The manuscript's canonical receiver routing: every internal cubic source
is sent to the first low-degree vertex selected by its ordered BFS trace. -/
noncomputable def routing
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) :
    Core.FiniteReceiverDischarge.Routing (input node88) where
  route := fun cubic => by
    let source : node63.typeAProfile.Cubic ctx.G.object :=
      ⟨cubic.1, (Core.FiniteReceiverDischarge.Input.mem_cubicSet_iff
        (input node88) cubic.1).1 cubic.2 |>.2⟩
    let receiver := node63.typeAProfile.receiverSelection ctx.G.object source |>.vertex
    refine ⟨receiver, ?_⟩
    exact (Core.FiniteReceiverDischarge.Input.mem_receiverSet_iff
      (input node88) receiver).2 ⟨Finset.mem_univ _,
        node63.typeAProfile.receiver_degree_le_two ctx.G.object source⟩

abbrev Saturated {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) :=
  (routing node88).Saturated

abbrev Unsaturated {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) : Prop :=
  (routing node88).Unsaturated

/-- The routing function is definitionally the terminal vertex of the exact
canonical trace. -/
theorem routedReceiver_eq_canonical
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87)
    (cubic : {vertex // vertex ∈ (input node88).cubicSet}) :
    ((routing node88).route cubic).1 =
      (node63.typeAProfile.receiverSelection ctx.G.object
        ⟨cubic.1, (Core.FiniteReceiverDischarge.Input.mem_cubicSet_iff
          (input node88) cubic.1).1 cubic.2 |>.2⟩).vertex := by
  rfl

/-- Yes payload on the original edge `[89] -> [93]`. -/
structure ToNode93 {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) where
  previous : Node88 node87
  exactPrevious : previous = node88
  saturated : Saturated node88
  receiver_mem : saturated.receiver ∈ (input node88).receiverSet
  receiver_degree_le_two :
    (input node88).degree saturated.receiver ≤ 2
  threshold_le_load :
    4 * (3 - (input node88).degree saturated.receiver) ≤
      (routing node88).load saturated.receiver

/-- No payload on the original edge `[89] -> [90]`. -/
structure ToNode90 {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) where
  previous : Node88 node87
  exactPrevious : previous = node88
  unsaturated : Unsaturated node88
  load_le_capacity : ∀ receiver ∈ (input node88).receiverSet,
    (routing node88).load receiver ≤
      4 * (3 - (input node88).degree receiver) - 1

/-- Exactly the two original outgoing edges of node `[89]`. -/
inductive Outcome {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87)
  | to93 : ToNode93 node88 → Outcome node88
  | to90 : ToNode90 node88 → Outcome node88

/-- Exhaustive saturation decision on the actual receiver fibres. -/
noncomputable def run
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) : Outcome node88 := by
  classical
  if saturated : Nonempty (routing node88).Saturated then
    let witness := Classical.choice saturated
    exact .to93 {
      previous := node88
      exactPrevious := rfl
      saturated := witness
      receiver_mem := witness.receiver_mem
      receiver_degree_le_two := witness.receiver_degree_le_two
      threshold_le_load := witness.threshold_le_load
    }
  else
    have unsaturated : (routing node88).Unsaturated := by
      rcases (routing node88).saturated_or_unsaturated with witness | unsaturated
      · exact False.elim (saturated witness)
      · exact unsaturated
    exact .to90 {
      previous := node88
      exactPrevious := rfl
      unsaturated := unsaturated
      load_le_capacity := unsaturated
    }

theorem run_exhaustive
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) :
    (∃ payload, run node88 = .to93 payload) ∨
      (∃ payload, run node88 = .to90 payload) := by
  cases run node88 with
  | to93 payload => exact Or.inl ⟨payload, rfl⟩
  | to90 payload => exact Or.inr ⟨payload, rfl⟩

/-- One receiver test per support vertex and one fibre comparison per actual
cubic-source/receiver pair. -/
noncomputable def localCheckCount
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (_node88 : Node88 node87) : Nat :=
  node63.typeAProfile.support.card + node63.typeAProfile.support.card ^ 2

theorem localCheckCount_polynomial
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) :
    localCheckCount node88 ≤
      ctx.G.object.input.vertices.card +
        ctx.G.object.input.vertices.card ^ 2 := by
  have supportLe : node63.typeAProfile.support.card ≤
      ctx.G.object.input.vertices.card := by
    rw [← ctx.G.object.card_vertexFinset]
    exact Finset.card_le_card fun vertex _ => ctx.G.object.mem_vertexFinset vertex
  exact Nat.add_le_add supportLe (Nat.pow_le_pow_left supportLe 2)

noncomputable def workBudget
    {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {node86 : Node86 node63} {node87 : Node87 node86}
    (node88 : Node88 node87) :
    Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.mk
    (fun _ => ctx.G.object.input.vertices.card)
    (fun _ => localCheckCount node88)
    2 2
    (by
      intro _
      have bound := localCheckCount_polynomial node88
      nlinarith)

end Erdos64EG.Internal.TypeANode89SaturationDecision
