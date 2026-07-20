import Erdos64EG.Node50

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [51]: high-entropy remainder bits

Node [51] consumes only the literal high constructor of node [50].  The
constrained-family entropy identity remains in the exact active predecessor;
this node multiplies the threshold inequality by the nonnegative remainder
size and records the paper's remainder-bit contribution.  It does not perform
the joint window--remainder accounting assigned to node [52].
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
        (node49RemainderGraphFamilyCount (Node21Context active.previous))

/-- Symbolic transport of node [49]'s exact entropy identity along the
literal node-[50] high edge.  The zero-remainder case is handled directly;
no family, graph, or local universe is enumerated. -/
noncomputable def node51Output {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual)
    (high : Node50High residual active) : Node51Output active high := by
  let cardR : ℝ :=
    (p13RemainderVertices (Node21Context active.previous)).card
  let logN : ℝ := Real.logb 2
    (Node21Context active.previous).G.object.input.vertices.card
  let logG : ℝ := Real.logb 2
    (node49RemainderGraphFamilyCount (Node21Context active.previous))
  have highExpanded := high
  change node50EntropyThreshold active.previous ≤
    node49RemainderEntropy (Node21Context active.previous) at highExpanded
  rw [active.output.entropyExact] at highExpanded
  have thresholdBound : (1 / 10 : ℝ) * logN ≤ logG / cardR := by
    simpa [node50EntropyThreshold, cardR, logN, logG] using highExpanded
  have cardRNonnegative : 0 ≤ cardR := by
    simp [cardR]
  have totalBudget : cardR * ((1 / 10 : ℝ) * logN) ≤ logG := by
    by_cases cardRZero : cardR = 0
    · have logGNonnegative : 0 ≤ logG := by
        by_cases countZero :
            node49RemainderGraphFamilyCount
                (Node21Context active.previous) = 0
        · simp [logG, countZero]
        · have countPositive :
              1 ≤ node49RemainderGraphFamilyCount
                (Node21Context active.previous) :=
            Nat.succ_le_of_lt (Nat.pos_of_ne_zero countZero)
          have countReal :
              (1 : ℝ) ≤
                node49RemainderGraphFamilyCount
                  (Node21Context active.previous) := by
            exact_mod_cast countPositive
          exact Real.logb_nonneg (by norm_num) countReal
      simpa [cardRZero] using logGNonnegative
    · have cardRPositive : 0 < cardR :=
        lt_of_le_of_ne' cardRNonnegative cardRZero
      have scaled :=
        mul_le_mul_of_nonneg_left thresholdBound cardRNonnegative
      have cancel : cardR * (logG / cardR) = logG := by
        field_simp [cardRZero]
      nlinarith
  exact {
    remainderBits := by
      calc
        (((p13RemainderVertices
              (Node21Context active.previous)).card : ℝ) / 10) *
              Real.logb 2
                (Node21Context active.previous).G.object.input.vertices.card =
            cardR * ((1 / 10 : ℝ) * logN) := by
              simp [cardR, logN]
              ring
        _ ≤ logG := totalBudget
        _ = Real.logb 2
              (node49RemainderGraphFamilyCount
                (Node21Context active.previous)) := rfl
  }

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
    (quietBlock : Node23DenseWindowQuietBlockInput V)
    (node48Input : Node48TypedYellowInput V)
    (residual : InitialResidual V) :=
  (runInitialThroughNode50 quietBlock node48Input
    residual).mapYesStage node51P13HighEntropyBranch

/-- Node [51] adds no finite semantic checks. -/
def node51LocalChecks : Nat := 0

theorem node51LocalChecks_eq_zero : node51LocalChecks = 0 := rfl

#print axioms node51P13HighEntropyBranch
#print axioms runInitialThroughNode51

end Erdos64EG.Internal
