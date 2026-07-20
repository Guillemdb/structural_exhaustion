import Erdos64EG.Shared.CT1
import Erdos64EG.Future.P13ColdGermLedger

namespace Erdos64EG.P13ColdGermTerminalRoutes

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}

abbrev ColdDyadicHit :=
  P13ColdGermLedger.ColdDyadicHit input ctx

abbrev ColdContextDistinction :=
  P13ColdGermLedger.ColdContextDistinction input boundaries ctx

abbrev ColdSilentExchange :=
  P13ColdGermLedger.ColdSilentExchange input boundaries ctx

abbrev ColdBoundedGerm :=
  P13ColdGermLedger.ColdBoundedGerm input boundaries ctx

/-! ## Node `[155]`: G1 executes the existing certificate-driven CT1 -/

/-- Convert the literal cycle carried by G1 into the existing edge-rooted
CT1 execution on the identical selected graph and inherited branch state. -/
def g1Run (hit : ColdDyadicHit (input := input) (ctx := ctx)) :=
  (input.fixed ctx.G.Vertex).runCycleAsRootedReturnCT1
    ctx.G.object ctx.baseline () hit.cycle

theorem g1_terminal (hit : ColdDyadicHit (input := input) (ctx := ctx)) :
    (g1Run hit).result.terminal = .c1 :=
  (g1Run hit).terminal_eq

theorem g1_trace (hit : ColdDyadicHit (input := input) (ctx := ctx)) :
    (g1Run hit).result.trace =
      [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal] :=
  (g1Run hit).trace_eq

theorem g1_checks (hit : ColdDyadicHit (input := input) (ctx := ctx)) :
    (g1Run hit).checks = 1 :=
  (g1Run hit).checks_eq

/-- The G1 CT1 hit contradicts the inherited target-avoiding context. -/
theorem g1_impossible (hit : ColdDyadicHit (input := input) (ctx := ctx)) : False :=
  ctx.avoids ⟨hit.cycle⟩

/-! ## Node `[156]`: G2 becomes the existing literal target-defect residual -/

/-- The raw context distinction is exactly the witness expected by the
existing boundaried target-defect endpoint.  No context search is repeated. -/
def g2TargetDefect
    (distinction : ColdContextDistinction
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      distinction.replacement distinction.atom.source :=
  ⟨distinction.outside, distinction.differs⟩

/-! ## Node `[157]`: G3 executes the existing literal CT3 compression -/

/-- Build the established graph-layer compression from the raw silent
same-interface exchange.  The graph layer derives the global smaller object,
baseline preservation, and target transport. -/
noncomputable def g3Compression
    (silent : ColdSilentExchange
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    MinimumDegreeCycleReplacement.Compression input boundaries silent.atom :=
  MinimumDegreeCycleReplacement.Compression.ofTargetComplete input boundaries
    silent.replacement silent.targetComplete silent.internalTargetFree
    silent.internalBaseline silent.locallySmaller

noncomputable def g3Run
    (silent : ColdSilentExchange
      (input := input) (boundaries := boundaries) (ctx := ctx)) :=
  (g3Compression silent).run

theorem g3_terminal
    (silent : ColdSilentExchange
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (g3Run silent).terminal = .compression :=
  (g3Compression silent).run_terminal

theorem g3_trace
    (silent : ColdSilentExchange
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (g3Run silent).trace =
      [.entry, .vectorComputation, .compressionSearch, .compressionTerminal] :=
  (g3Compression silent).run_trace

theorem g3_checks
    (silent : ColdSilentExchange
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (g3Run silent).checks = 1 :=
  (g3Compression silent).run_checks

theorem g3_total
    (silent : ColdSilentExchange
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    ∃ result : CT3.CertifiedCompressionRun ctx
        (g3Compression silent).certifiedInput,
      result.terminal = .compression ∧
        result.trace =
          [.entry, .vectorComputation, .compressionSearch,
            .compressionTerminal] :=
  (g3Compression silent).run_total

/-- The G3 literal CT3 execution closes by minimality. -/
theorem g3_impossible
    (silent : ColdSilentExchange
      (input := input) (boundaries := boundaries) (ctx := ctx)) : False :=
  (g3Compression silent).impossible

/-! ## Exhaustive terminal routing downstream of a supplied germ -/

/-- Exact target-defect residual retained by G2.  The raw distinction remains
bundled with the defect it generated, so neither representative can be
silently exchanged for a different germ. -/
def TargetDefectResidual : Prop :=
  ∃ distinction : ColdContextDistinction
      (input := input) (boundaries := boundaries) (ctx := ctx),
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      distinction.replacement distinction.atom.source

/-- After the classifier's G1 and G3 branches execute their existing closing
machines, the only retained output is the exact G2 distinction and its target
defect. -/
theorem targetDefect_of_outcome
    (germ : ColdBoundedGerm
      (input := input) (boundaries := boundaries) (ctx := ctx))
    (outcome : germ.Outcome) :
    TargetDefectResidual
      (input := input) (boundaries := boundaries) (ctx := ctx) := by
  cases outcome with
  | g1 hit => exact (g1_impossible hit).elim
  | g2 distinction => exact ⟨distinction, g2TargetDefect distinction⟩
  | g3 silent => exact (g3_impossible silent).elim

/-- Execute the classifier of one supplied `ColdBoundedGerm` and route all
three outputs.  This adapter neither constructs the germ nor supplies its
finite-context coverage theorem; those remain predecessor obligations. -/
noncomputable def route
    (germ : ColdBoundedGerm
      (input := input) (boundaries := boundaries) (ctx := ctx))
    (lengthChanging : germ.increment ≠ 0) :
    TargetDefectResidual
      (input := input) (boundaries := boundaries) (ctx := ctx) :=
  targetDefect_of_outcome germ (germ.classify lengthChanging)

end Erdos64EG.P13ColdGermTerminalRoutes
