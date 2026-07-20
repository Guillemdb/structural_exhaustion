import Erdos64EG.Node19
import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureCertificate
import StructuralExhaustion.Core.FiniteBitRelationBarrier

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Public data API for diagram node [21]

This module fixes the exact type-level boundary between the finite node-[21]
enumeration and every later paper node.  It contains the concrete finite data
named by node [21] and the exact accumulated-stage output type, but no audit,
enumeration theorem, or producer.  The computation-heavy proofs live in
`CT10P13MultiScaleCurvature`; downstream nodes can therefore consume an
already verified output without replaying that producer.
-/

abbrev P13BarrierCandidate := Fin 14 × Fin 14

def P13BarrierAccepted (candidate : P13BarrierCandidate) : Prop :=
  candidate.1.1 + candidate.2.1 < 13

def p13BarrierAcceptedDecidable (candidate : P13BarrierCandidate) :
    Decidable (P13BarrierAccepted candidate) := by
  unfold P13BarrierAccepted
  infer_instance

/-- The exact CT10 classification of the paper's ordered positive length
pairs `(a,b)` with `a+b ≤ 14`. -/
def p13BarrierClassification :
    CT10.ExhaustiveClassification.Profile P13BarrierCandidate where
  candidates := inferInstance
  Accepts := P13BarrierAccepted
  acceptsDecidable := p13BarrierAcceptedDecidable

abbrev P13BarrierIndex := p13BarrierClassification.Class

def P13BarrierIndex.leftLength (index : P13BarrierIndex) : Nat :=
  index.1.1.1 + 1

def P13BarrierIndex.rightLength (index : P13BarrierIndex) : Nat :=
  index.1.2.1 + 1

/-- The fixed packed compatibility rows used by the node-[21] finite
certificate.  Their graph semantics are proved by the producer module. -/
def p13MultiScaleBarrierProfile :
    Core.FiniteBitRelationBarrier.Profile 399 :=
  P13MultiScaleCurvatureCertificate.profile

def p13BarrierSafeCount (index : P13BarrierIndex) : Nat :=
  P13MultiScaleCurvatureCertificate.safeCount
    index.leftLength index.rightLength

def p13BarrierFlatCount (index : P13BarrierIndex) : Nat :=
  P13MultiScaleCurvatureCertificate.flatCount
    index.leftLength index.rightLength

def p13BarrierObstructedCount (index : P13BarrierIndex) : Nat :=
  p13BarrierSafeCount index - p13BarrierFlatCount index

def p13BarrierSafeProduct : Nat :=
  (p13BarrierClassification.classes.orderedValues.map
    p13BarrierSafeCount).prod

def p13BarrierFlatProduct : Nat :=
  (p13BarrierClassification.classes.orderedValues.map
    p13BarrierFlatCount).prod

/-- The symbolic work expression whose polynomial bound is proved by the
node-[21] producer. -/
def p13MultiScaleCheckCount : Nat :=
  p13BarrierClassification.checks + 91 * (399 + 399 ^ 2)

/-- Thin mathematical interface consumed by the sequential hot/cold window
ledger.  It deliberately contains no predecessor, handoff, or routing data:
the accumulated framework stage owns all transport. -/
structure P13BarrierRateCertificate : Prop where
  rateFloor : 2 ^ 118 * p13BarrierFlatProduct < p13BarrierSafeProduct

/-! ## Exact paper-node interface -/

abbrev Node21Context {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual) :=
  Node18Context node18.previous

/-- Only the mathematics certified at node `[21]`.  The predecessor and full
accumulated ledger remain framework-owned and are not copied into this
payload. -/
structure Node21Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18) : Type (u + 1) where
  stage : p13BarrierClassification.VerifiedStage
    (Node21Context node18).toBranchContext
  barrierCount : p13BarrierClassification.classCount = 91
  certificate : Core.FiniteBitRelationBarrier.CertifiedTable
    p13MultiScaleBarrierProfile
    (Fin 15) (fun length => length.1)
    (fun length => P13MultiScaleCurvatureCertificate.semanticRelation length.1)
    P13BarrierIndex
  wellFormed : ∀ index : P13BarrierIndex,
    0 < p13BarrierFlatCount index ∧
      p13BarrierFlatCount index ≤ p13BarrierSafeCount index
  rateFloor : 2 ^ 118 * p13BarrierFlatProduct < p13BarrierSafeProduct
  oneOneCounts :
    P13MultiScaleCurvatureCertificate.safeCount 1 1 = 543958 ∧
      P13MultiScaleCurvatureCertificate.safeCount 1 1 -
          P13MultiScaleCurvatureCertificate.flatCount 1 1 = 432672 ∧
      P13MultiScaleCurvatureCertificate.flatCount 1 1 = 111286
  terminal :
    (p13BarrierClassification.run
      (Node21Context node18).toBranchContext).terminal = .exhaustive
  trace :
    (p13BarrierClassification.run
      (Node21Context node18).toBranchContext).trace =
      [.entry, .table, .direct, .missing, .exhaustiveTerminal]
  polynomial : p13MultiScaleCheckCount ≤ 92 * (399 + 1) ^ 2
  nearCubicBudget :
    (Graph.InducedPathWindowLedger.totalSurplus
      (Node21Context node18).G.object) ^ 2 ≤
      node19SurplusCoefficient *
        (Node21Context node18).G.object.input.vertices.card

/-- Extract the only node-[21] fact needed by the compatible-extension
ledger.  Later nodes retrieve `Node21Output` from the accumulated stage and
form this view without reconstructing any earlier proof object. -/
def Node21Output.barrierRateCertificate {V : Type u}
    {residual : InitialResidual V} {node18 : Node18Stage residual}
    {bounded : Node19Low residual node18}
    (output : Node21Output node18 bounded) : P13BarrierRateCertificate where
  rateFloor := output.rateFloor

/-- Exact existing diagram edge `[19] no -> [21]`. -/
abbrev Node21Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionNoContinuation
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded) residual

end Erdos64EG.Internal
