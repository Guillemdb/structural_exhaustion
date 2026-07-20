import Erdos64EG.Node50

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [51]: high-entropy remainder bits

Node [51] consumes only the literal high constructor of node [50].  It takes
base-two logarithms of that exact natural-power inequality and records the
paper's remainder-bit contribution.  It does not perform the joint
window--remainder accounting assigned to node [52].
-/

/-- The single new mathematical conclusion at node [51]. -/
structure Node51Output {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual)
    (_high : Node50High residual active) : Type (u + 2) where
  remainderBits :
    (((p13RemainderVertices (Node21Context active.previous)).card : ℝ) / 10) *
        Real.logb 2
          (Node21Context active.previous).G.object.input.vertices.card ≤
      Real.logb 2
        (active.output.stateCount)

/-- Take logarithms of node [50]'s exact natural-power inequality.  The
zero-vertex case is handled directly; no family, graph, or local universe is
enumerated. -/
noncomputable def node51Output {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual)
    (high : Node50High residual active) : Node51Output active high := by
  let n := (Node21Context active.previous).G.object.input.vertices.card
  let r := (p13RemainderVertices (Node21Context active.previous)).card
  let count := active.output.stateCount
  have highPower : n ^ r ≤ count ^ 10 := by
    simpa [n, r, count] using high
  refine { remainderBits := ?_ }
  by_cases nZero : n = 0
  · have partition := p13Remainder_partition (Node21Context active.previous)
    have rZero : r = 0 := by
      dsimp [r, n] at partition ⊢
      omega
    have logCountNonnegative : 0 ≤ Real.logb 2 count := by
      by_cases countZero : count = 0
      · simp [countZero]
      · apply Real.logb_nonneg (by norm_num)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr countZero
    simpa [n, r, count, nZero, rZero] using logCountNonnegative
  · have nPositive : 0 < n := Nat.pos_of_ne_zero nZero
    have countPositive : 0 < count := by
      by_contra countNotPositive
      have countZero : count = 0 := Nat.eq_zero_of_not_pos countNotPositive
      rw [countZero] at highPower
      have powerPositive : 0 < n ^ r := Nat.pow_pos nPositive
      omega
    have highPowerReal : (n : ℝ) ^ r ≤ (count : ℝ) ^ 10 := by
      exact_mod_cast highPower
    have logged :
        Real.logb 2 ((n : ℝ) ^ r) ≤
          Real.logb 2 ((count : ℝ) ^ 10) :=
      (Real.logb_le_logb (by norm_num)
        (pow_pos (by exact_mod_cast nPositive) r)
        (pow_pos (by exact_mod_cast countPositive) 10)).2 highPowerReal
    rw [Real.logb_pow, Real.logb_pow] at logged
    dsimp [n, r, count] at logged ⊢
    norm_num at logged ⊢
    linarith

/-- Exact `[50] --yes--> [51]` continuation.  Core transports the bypass and
the node-[50] low leaf without application-owned routing. -/
abbrev Node51Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node50Bypass V) (Node50Active V)
    (@Node50High V) (@Node50Low V)
    (fun residual active high =>
      Node51Output (residual := residual) active high)
    residual

noncomputable def node51P13HighEntropyBranch {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node50Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node51Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
    fun _residual active high => node51Output active high

noncomputable def runInitialThroughNode51 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode50 residual).mapYesStage
    node51P13HighEntropyBranch

/-- Node [51] adds no finite semantic checks. -/
def node51LocalChecks : Nat := 0

theorem node51LocalChecks_eq_zero : node51LocalChecks = 0 := rfl

#print axioms node51P13HighEntropyBranch
#print axioms runInitialThroughNode51

end Erdos64EG.Internal
