import Erdos64EG.InternalProblem
import StructuralExhaustion.Core.FiniteBoundedOverlap
import StructuralExhaustion.Core.FiniteFirstFailure
import StructuralExhaustion.Core.FinitePriorityOptionScanWork
import StructuralExhaustion.Graph.InducedPathColdLedger
import StructuralExhaustion.Graph.PackedBoundariedGluing
import StructuralExhaustion.CT10.ExhaustiveClassification
import Mathlib.Tactic

namespace Erdos64EG.P13ColdGermLedger

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u

/-!
# Cold `P13` germ ledger (nodes 151--154)

The graph arithmetic for nodes 151--152 lives in
`Graph.InducedPathColdLedger`.  This file fixes the proof-carrying local
payloads and the exhaustive bounded-germ classifier used at nodes 153--154.
Every context scan is over a germ-local `FinEnum`; the supplied reflection
theorem relates that finite code table to all literal compatible gluing
contexts.  No ambient graph, context, piece, or completion universe is
enumerated.
-/

variable (input : PackedMinimumDegreeCycle.StaticInput)
variable {T : Type u} (boundaries : FinEnum T) [Nonempty T]
variable (ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target)

abbrev Atom :=
  MinimumDegreeCycleReplacement.ProperAtom input boundaries ctx

/-- Raw G1 payload: an actual cycle in the inherited ambient graph, together
with the cold-window offset that produced it. -/
structure ColdDyadicHit where
  offset : Fin 13
  cycle : CycleWithLength ctx.G.object.graph input.LengthOK

/-- Raw G2 payload: one literal compatible gluing context that distinguishes
the two same-interface representatives.  It is intentionally not a prebuilt
target-defect residual. -/
structure ColdContextDistinction where
  atom : Atom input boundaries ctx
  replacement : Piece T
  outside : Context T
  differs : ¬(input.Target (glue boundaries replacement outside) ↔
    input.Target (glue boundaries atom.source outside))

/-- Raw G3 payload: the literal atom and replacement data needed by
`Compression.ofTargetComplete`.  It is intentionally not a prebuilt CT3
input. -/
structure ColdSilentExchange where
  atom : Atom input boundaries ctx
  replacement : Piece T
  targetComplete : MinimumDegreeCycleReplacement.TargetComplete input
    boundaries replacement atom.source
  internalTargetFree : ¬input.Target (Piece.pack boundaries replacement)
  internalBaseline : replacement.InternalBaseline boundaries input.minimumDegree
  locallySmaller : Piece.LexSmaller replacement atom.source

/-- One bounded same-interface germ.  `ContextCode` is the exact finite
response table named by the manuscript.  `contextCoverage` is the symbolic
reflection theorem: every literal outside context has the same two truth
values as some local code. -/
structure ColdBoundedGerm where
  atom : Atom input boundaries ctx
  replacement : Piece T
  boundaryDegree_eq :
    MinimumDegreeCycleReplacement.BoundaryDegreeProfile boundaries replacement =
      MinimumDegreeCycleReplacement.BoundaryDegreeProfile boundaries atom.source
  /-- Manuscript increment `|E| - |Q|`, with `E` the actual atom source and
  `Q` the canonical same-interface representative. -/
  increment : Int
  increment_eq : increment =
    Int.ofNat atom.source.edgeCount - Int.ofNat replacement.edgeCount
  hit? : Option (ColdDyadicHit input ctx)
  ContextCode : Type u
  contexts : FinEnum ContextCode
  decodeContext : ContextCode → Context T
  replacementResponse : ContextCode → Bool
  sourceResponse : ContextCode → Bool
  replacementResponse_reflect : ∀ code,
    (replacementResponse code = true ↔
      input.Target (glue boundaries replacement (decodeContext code)))
  sourceResponse_reflect : ∀ code,
    (sourceResponse code = true ↔
      input.Target (glue boundaries atom.source (decodeContext code)))
  contextCoverage : ∀ outside : Context T, ∃ code : ContextCode,
    (input.Target (glue boundaries replacement outside) ↔
      replacementResponse code = true) ∧
    (input.Target (glue boundaries atom.source outside) ↔
      sourceResponse code = true)
  /-- Admissibility and strict orientation are demanded only after the local
  response table is silent and has therefore produced target completeness.
  This keeps the bounded germ neutral while retaining the original G3 route. -/
  silentExchangeOfTargetComplete :
    increment ≠ 0 →
    MinimumDegreeCycleReplacement.TargetComplete input boundaries
      replacement atom.source →
    ColdSilentExchange input boundaries ctx

namespace ColdBoundedGerm

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}

def Distinguishes (germ : ColdBoundedGerm input boundaries ctx)
    (code : germ.ContextCode) : Prop :=
  germ.replacementResponse code ≠ germ.sourceResponse code

def distinguishesDecidable (germ : ColdBoundedGerm input boundaries ctx)
    (code : germ.ContextCode) : Decidable (germ.Distinguishes code) := by
  unfold Distinguishes
  cases Bool.decEq (germ.replacementResponse code)
      (germ.sourceResponse code) with
  | isTrue equal => exact .isFalse fun notEqual => notEqual equal
  | isFalse notEqual => exact .isTrue notEqual

def contextScan (germ : ColdBoundedGerm input boundaries ctx) :=
  Core.FiniteSearch.first germ.contexts germ.Distinguishes
    germ.distinguishesDecidable

/-- Exhaustive G1/G2/G3 output. -/
inductive Outcome (germ : ColdBoundedGerm input boundaries ctx) where
  | g1 (hit : ColdDyadicHit input ctx)
  | g2 (distinction : ColdContextDistinction input boundaries ctx)
  | g3 (silent : ColdSilentExchange input boundaries ctx)

private theorem bool_true_iff_of_eq {left right : Bool} (equal : left = right) :
    (left = true ↔ right = true) := by simp [equal]

private noncomputable def distinctionOfHit
    (germ : ColdBoundedGerm input boundaries ctx)
    (found : Core.FiniteSearch.FirstHit germ.contexts.orderedValues
      germ.Distinguishes) :
    ColdContextDistinction input boundaries ctx := by
  refine {
    atom := germ.atom
    replacement := germ.replacement
    outside := germ.decodeContext found.value
    differs := ?_
  }
  intro targetIff
  have boolIff : germ.replacementResponse found.value = true ↔
      germ.sourceResponse found.value = true :=
    (germ.replacementResponse_reflect found.value).trans
      (targetIff.trans (germ.sourceResponse_reflect found.value).symm)
  have responsesEqual : germ.replacementResponse found.value =
      germ.sourceResponse found.value := by
    cases leftEq : germ.replacementResponse found.value <;>
      cases rightEq : germ.sourceResponse found.value <;>
      simp [leftEq, rightEq] at boolIff ⊢
  exact found.holds responsesEqual

private noncomputable def silentOfAbsent
    (germ : ColdBoundedGerm input boundaries ctx)
    (lengthChanging : germ.increment ≠ 0)
    (absent : ∀ code, code ∈ germ.contexts.orderedValues →
      ¬germ.Distinguishes code) :
    ColdSilentExchange input boundaries ctx := by
  apply germ.silentExchangeOfTargetComplete lengthChanging
  refine ⟨germ.boundaryDegree_eq, ?_⟩
  intro outside
  rcases germ.contextCoverage outside with ⟨code, replacementIff, sourceIff⟩
  have noDistinction := absent code (germ.contexts.mem_orderedValues code)
  have responsesEqual : germ.replacementResponse code =
      germ.sourceResponse code := not_ne_iff.mp noDistinction
  exact replacementIff.trans
    ((bool_true_iff_of_eq responsesEqual).trans sourceIff.symm)

/-- Finite, priority-ordered germ classification backend for node `[154]`.
This classifies one already constructed local germ; it does not construct the
germ or prove that a supplied germ table covers all graph-theoretic germs.  G3 is
constructed only after the literal hit option is empty and the entire local
context-code table has no distinction. -/
noncomputable def classify (germ : ColdBoundedGerm input boundaries ctx)
    (lengthChanging : germ.increment ≠ 0) :
    germ.Outcome :=
  match germ.hit? with
  | some hit => .g1 hit
  | none =>
      match germ.contextScan with
      | .found found => .g2 (germ.distinctionOfHit found)
      | .absent absent => .g3 (germ.silentOfAbsent lengthChanging absent)

/-- Exact node-[154] trace labels, including the selected original terminal. -/
inductive ClassifierStep where
  | literalHitCheck
  | finiteResponseScan
  | g1Terminal
  | g2Terminal
  | g3Terminal
  deriving DecidableEq, Repr

/-- Observable priority trace of the exact node-[154] classifier.  A literal
hit stops at G1; only its absence enables the finite response-code scan, whose
first distinction reaches G2 and whose exhaustive absence reaches G3. -/
noncomputable def classifyTrace
    (germ : ColdBoundedGerm input boundaries ctx) : List ClassifierStep :=
  match germ.hit? with
  | some _ => [.literalHitCheck, .g1Terminal]
  | none =>
      match germ.contextScan with
      | .found _ => [.literalHitCheck, .finiteResponseScan, .g2Terminal]
      | .absent _ => [.literalHitCheck, .finiteResponseScan, .g3Terminal]

theorem classifyTrace_length_le_three
    (germ : ColdBoundedGerm input boundaries ctx) :
    germ.classifyTrace.length ≤ 3 := by
  cases hitEq : germ.hit? with
  | some hit => simp [classifyTrace, hitEq]
  | none =>
      cases scanEq : germ.contextScan <;>
        simp [classifyTrace, hitEq, scanEq]

/-- Local classifier checks: one literal-hit test and, only on failure, one
pass over the germ's declared response-code schedule. -/
def classifyChecks (germ : ColdBoundedGerm input boundaries ctx) : Nat :=
  Core.FinitePriorityOptionScanWork.checks germ.hit? germ.contexts

theorem classifyChecks_le_codes_add_one
    (germ : ColdBoundedGerm input boundaries ctx) :
    germ.classifyChecks ≤ germ.contexts.card + 1 :=
  Core.FinitePriorityOptionScanWork.checks_le_codes_add_one
    germ.hit? germ.contexts

theorem classifyChecks_linear
    (germ : ColdBoundedGerm input boundaries ctx) :
    germ.classifyChecks ≤ 2 * (germ.contexts.card + 1) :=
  Core.FinitePriorityOptionScanWork.checks_linear germ.hit? germ.contexts

/-- The three original outcomes are exhaustive, with their exact priority
trace.  The second and third alternatives are reached only after the optional
literal hit is absent and the declared finite response-code scan runs. -/
theorem classify_exhaustive_with_trace
    (germ : ColdBoundedGerm input boundaries ctx)
    (lengthChanging : germ.increment ≠ 0) :
    (∃ hit, germ.classify lengthChanging = .g1 hit ∧
      germ.classifyTrace = [.literalHitCheck, .g1Terminal]) ∨
    (∃ distinction, germ.classify lengthChanging = .g2 distinction ∧
      germ.classifyTrace =
        [.literalHitCheck, .finiteResponseScan, .g2Terminal]) ∨
    (∃ silent, germ.classify lengthChanging = .g3 silent ∧
      germ.classifyTrace =
        [.literalHitCheck, .finiteResponseScan, .g3Terminal]) := by
  cases hitEq : germ.hit? with
  | some hit =>
      exact Or.inl ⟨hit, by simp [classify, classifyTrace, hitEq], by
        simp [classifyTrace, hitEq]⟩
  | none =>
      cases scanEq : germ.contextScan with
      | found found =>
          exact Or.inr (Or.inl ⟨germ.distinctionOfHit found,
            by simp [classify, hitEq, scanEq], by
              simp [classifyTrace, hitEq, scanEq]⟩)
      | absent absent =>
          exact Or.inr (Or.inr ⟨germ.silentOfAbsent lengthChanging absent,
            by simp [classify, hitEq, scanEq], by
              simp [classifyTrace, hitEq, scanEq]⟩)

end ColdBoundedGerm

/-! ## Exhaustive finite same-interface table (CT10) -/

/-- Explicit finite universe of bounded same-interface germ rows.  The row
type is local and supplied directly; CT10 constructs and verifies the exact
accepted table rather than enumerating pieces or contexts. -/
structure GermTable (Candidate : Type u) where
  candidates : FinEnum Candidate
  germ : Candidate → ColdBoundedGerm input boundaries ctx
  lengthChanging : ∀ candidate, (germ candidate).increment ≠ 0

namespace GermTable

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}
variable {Candidate : Type u}
variable (table : GermTable input boundaries ctx Candidate)

/-- CT10 candidate predicate.  Every supplied row is accepted; the finite
candidate type itself is the exact manuscript table. -/
def classificationProfile :
    CT10.ExhaustiveClassification.Profile Candidate where
  candidates := table.candidates
  Accepts := fun _ ↦ True
  acceptsDecidable := fun _ ↦ .isTrue trivial

abbrev Class := table.classificationProfile.Class

def decodedGerm (row : table.Class) :
    ColdBoundedGerm input boundaries ctx := table.germ row.1

noncomputable def classificationRun :=
  table.classificationProfile.run ctx.toBranchContext

/-- CT10 reaches its exhaustive terminal for the exact supplied candidate
table.  This theorem deliberately makes no graph-level coverage claim. -/
theorem classification_terminal :
    table.classificationRun.terminal = .exhaustive :=
  table.classificationProfile.run_terminal_exhaustive ctx.toBranchContext

theorem classification_trace : table.classificationRun.trace =
    [.entry, .table, .direct, .missing, .exhaustiveTerminal] :=
  table.classificationProfile.run_trace ctx.toBranchContext

def verifiedClassification :
    table.classificationProfile.VerifiedStage ctx.toBranchContext :=
  table.classificationProfile.verifiedStage ctx.toBranchContext

/-- Every exact CT10 row receives one computed G1/G2/G3 outcome. -/
noncomputable def classifyRow (row : table.Class) :
    (table.decodedGerm row).Outcome :=
  (table.decodedGerm row).classify (table.lengthChanging row.1)

/-- Candidate-classifier plus CT10 work schedule, quadratic only in the
explicit local table cardinality. -/
theorem polynomial : table.classificationProfile.checks ≤
    table.classificationProfile.budget.coefficient *
      (table.classificationProfile.budget.size () + 1) ^
        table.classificationProfile.budget.degree :=
  table.classificationProfile.budget.bounded ()

end GermTable

end Erdos64EG.P13ColdGermLedger
