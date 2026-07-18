import Erdos64EG.P13ColdTargetDefectHandoff

namespace Erdos64EG.P13ColdGermTableConsumers

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}

abbrev ColdBoundedGerm :=
  P13ColdGermLedger.ColdBoundedGerm input boundaries ctx

abbrev RoutedResidual :=
  P13ColdTargetDefectHandoff.RoutedResidual
    (input := input) (boundaries := boundaries) (ctx := ctx)

/-- Consume one exact G1/G2/G3 result without first erasing G2's selected
distinguishing context behind an existential.  G1 closes by the inherited
target-avoidance proof, G3 closes by the established literal CT3 compression,
and G2 retains the exact two representatives and outside context. -/
noncomputable def routeOutcome
    {germ : ColdBoundedGerm (input := input) (boundaries := boundaries)
      (ctx := ctx)}
    (outcome : germ.Outcome) :
    RoutedResidual (input := input) (boundaries := boundaries) (ctx := ctx) :=
  match outcome with
  | .g1 hit => (P13ColdGermTerminalRoutes.g1_impossible hit).elim
  | .g2 distinction =>
      P13ColdTargetDefectHandoff.routeDistinction distinction
  | .g3 silent => (P13ColdGermTerminalRoutes.g3_impossible silent).elim

@[simp] theorem routeOutcome_g2_distinction
    {germ : ColdBoundedGerm (input := input) (boundaries := boundaries)
      (ctx := ctx)}
    (distinction : P13ColdGermLedger.ColdContextDistinction
      input boundaries ctx) :
    (routeOutcome (germ := germ) (.g2 distinction)).distinction = distinction :=
  rfl

@[simp] theorem routeOutcome_g2_outside
    {germ : ColdBoundedGerm (input := input) (boundaries := boundaries)
      (ctx := ctx)}
    (distinction : P13ColdGermLedger.ColdContextDistinction
      input boundaries ctx) :
    (routeOutcome (germ := germ) (.g2 distinction)).residual.source.outside =
      distinction.outside :=
  rfl

/-- Provenance-preserving consumer for one exact finite same-interface row. -/
noncomputable def routeGerm
    (germ : ColdBoundedGerm (input := input) (boundaries := boundaries)
      (ctx := ctx))
    (lengthChanging : germ.increment ≠ 0) :
    RoutedResidual (input := input) (boundaries := boundaries) (ctx := ctx) :=
  routeOutcome (germ.classify lengthChanging)

theorem routeGerm_targetDefective
    (germ : ColdBoundedGerm (input := input) (boundaries := boundaries)
      (ctx := ctx))
    (lengthChanging : germ.increment ≠ 0) :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetDefective input
      boundaries (routeGerm germ lengthChanging).residual.source.left
        (routeGerm germ lengthChanging).residual.source.right :=
  (routeGerm germ lengthChanging).residual.source.targetDefective

theorem routeGerm_ambient
    (germ : ColdBoundedGerm (input := input) (boundaries := boundaries)
      (ctx := ctx))
    (lengthChanging : germ.increment ≠ 0) :
    (routeGerm germ lengthChanging).residual.source.branch.G = ctx.G :=
  Routes.TargetDefectHandoff.ambient_preserved input boundaries ctx
    (routeGerm germ lengthChanging).residual.source

namespace GermTable

variable {Candidate : Type u}

abbrev Table (Candidate : Type u) :=
  P13ColdGermLedger.GermTable input boundaries ctx Candidate

/-- Route one exact CT10 table row through the pointwise G1--G3 consumers.
The decoded germ is the very row selected by CT10; no second table lookup or
context search is performed. -/
noncomputable def routeRow
    (table : Table (input := input) (boundaries := boundaries) (ctx := ctx)
      Candidate)
    (row : table.Class) :
    RoutedResidual (input := input) (boundaries := boundaries) (ctx := ctx) :=
  routeOutcome (table.classifyRow row)

theorem routeRow_targetDefective
    (table : Table (input := input) (boundaries := boundaries) (ctx := ctx)
      Candidate)
    (row : table.Class) :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetDefective input
      boundaries (routeRow table row).residual.source.left
        (routeRow table row).residual.source.right :=
  (routeRow table row).residual.source.targetDefective

theorem routeRow_ambient
    (table : Table (input := input) (boundaries := boundaries) (ctx := ctx)
      Candidate)
    (row : table.Class) :
    (routeRow table row).residual.source.branch.G = ctx.G :=
  Routes.TargetDefectHandoff.ambient_preserved input boundaries ctx
    (routeRow table row).residual.source

/-- Proof object tying the routed residual to the exact selected table row. -/
structure VerifiedRowRouting
    (table : Table (input := input) (boundaries := boundaries) (ctx := ctx)
      Candidate)
    (row : table.Class) where
  residual : RoutedResidual
    (input := input) (boundaries := boundaries) (ctx := ctx)
  exact : residual = routeRow table row

/-- Every row of the explicit local table has a provenance-preserving typed
consumer tied definitionally to that row's decoded germ.  This is deliberately
row-local and makes no graph-to-table coverage claim. -/
noncomputable def verifiedRowRouting
    (table : Table (input := input) (boundaries := boundaries) (ctx := ctx)
      Candidate)
    (row : table.Class) : VerifiedRowRouting table row :=
  ⟨routeRow table row, rfl⟩

theorem verifiedRowRouting_targetDefective
    (table : Table (input := input) (boundaries := boundaries) (ctx := ctx)
      Candidate)
    (row : table.Class) :
    PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetDefective input
      boundaries (verifiedRowRouting table row).residual.residual.source.left
        (verifiedRowRouting table row).residual.residual.source.right :=
  (verifiedRowRouting table row).residual.residual.source.targetDefective

end GermTable

end Erdos64EG.P13ColdGermTableConsumers
