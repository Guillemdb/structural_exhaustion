import HypostructureErdos64EG.Node63
import HypostructureErdos64EG.Node164
import Hypostructure.Core.Strategy

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-! The official proposition is consumed only at the public target boundary.
The graph layer supplies the finite instances and the registered target
equivalence; the strategy layer continues to operate on residual stages. -/

theorem officialStatement_target
    (official : officialStatement.{u})
    (residual : InitialResidual.{u}) :
    Target residual.object := by
  change OfficialStatement at official
  letI : Fintype residual.object.Vertex :=
    @FinEnum.instFintype _ residual.object.vertices
  letI : DecidableRel residual.object.graph.Adj := residual.object.decideAdj
  apply (target_iff_official_conclusion residual.object).mpr
  simpa [Baseline] using
    official residual.object.Vertex residual.object.graph residual.baseline

/-- Core-owned exhaustive strategy for the final Node 62 split.  The branch
payloads are proof data from the predecessor stage; Core owns classification
and the closed branch algebra. -/
noncomputable def node62Strategy
    {Previous : Type u} (contract : Node62Contract Previous) :
    Core.Strategy.ClosedDichotomy (Node62Stage contract) where
  LeftPayload stage := Core.Strategy.ProofPayload
    (Node62NoHighSurplus contract stage.previous)
  RightPayload stage := Core.Strategy.ProofPayload
    (Node62HighSurplus contract stage.previous)
  classify stage := match stage.added with
    | .yesBranch high => Sum.inr ⟨high⟩
    | .noBranch noHigh => Sum.inl ⟨noHigh⟩
  leftClosed stage _proof :=
    Node62NoHighSurplus contract stage.previous
  rightClosed stage _proof :=
    Node62HighSurplus contract stage.previous
  leftProof stage := by
    cases added : stage.added with
    | yesBranch high => simp [added]
    | noBranch noHigh => simpa [added] using noHigh
  rightProof stage := by
    cases added : stage.added with
    | yesBranch high => simpa [added] using high
    | noBranch noHigh => simp [added]

/-! The paper's Type-A/Type-B checkpoint is the public destructor for the
framework-owned Node 62 decision.  It introduces no new routing or problem
data: the literal predecessor and its branch proof are already carried by the
Core ledger extension. -/

theorem only_type_A_or_B
    {Previous : Type u} (contract : Node62Contract Previous)
    (stage : Node62Stage contract) :
    (∃ (previous : Previous),
      ∃ (high : Node62HighSurplus contract previous),
        stage = Core.Residual.Ledger.extend previous
          (Core.Residual.Decision.Binary.yesBranch high)) ∨
    (∃ (previous : Previous),
      ∃ (noHigh : Node62NoHighSurplus contract previous),
        stage = Core.Residual.Ledger.extend previous
          (Core.Residual.Decision.Binary.noBranch noHigh)) := by
  cases h : stage.added with
  | yesBranch high =>
      exact Or.inl ⟨stage.previous, high, by
        calc
          stage = Core.Residual.Ledger.extend stage.previous stage.added :=
            (Core.Residual.Ledger.extend_eta stage).symm
          _ = Core.Residual.Ledger.extend stage.previous
              (Core.Residual.Decision.Binary.yesBranch high) := by rw [h]
      ⟩
  | noBranch noHigh =>
      exact Or.inr ⟨stage.previous, noHigh, by
        calc
          stage = Core.Residual.Ledger.extend stage.previous stage.added :=
            (Core.Residual.Ledger.extend_eta stage).symm
          _ = Core.Residual.Ledger.extend stage.previous
              (Core.Residual.Decision.Binary.noBranch noHigh) := by rw [h]
      ⟩

end HypostructureErdos64EG
