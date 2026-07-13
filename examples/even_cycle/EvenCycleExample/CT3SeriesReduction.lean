import EvenCycleExample.CT1Instance
import StructuralExhaustion.CT3.TargetCompression
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace EvenCycleExample.SeriesReduction

open StructuralExhaustion

/-!
# Duffin parity-series reduction

Two-terminal paths are represented canonically by their length.  Gluing a
nonempty return path produces the corresponding cycle graph, while the empty
context leaves a path graph.  CT3 sees only the four local response
coordinates below.  Their correctness is proved structurally from acyclicity
of paths and rigidity of connected 2-regular graphs; no cycle universe is
generated.
-/

inductive Piece where
  | evenCanonical
  | oddCanonical
  | evenLong
  | oddLong
  deriving Repr, DecidableEq

inductive Context where
  | empty
  | evenReturn
  | oddReturn
  | targetPresent
  deriving Repr, DecidableEq

inductive Parity where
  | even
  | odd
  deriving Repr, DecidableEq

abbrev Candidate := Parity
abbrev Row := Parity

@[implicit_reducible]
def contexts : FinEnum Context :=
  FinEnum.ofNodupList
    [.empty, .evenReturn, .oddReturn, .targetPresent]
    (by intro context; cases context <;> simp) (by decide)

@[implicit_reducible]
def parities : FinEnum Parity :=
  FinEnum.ofNodupList [.even, .odd]
    (by intro parity; cases parity <;> simp) (by decide)

/-- Edge length of each two-terminal path. -/
def Piece.length : Piece → Nat
  | .evenCanonical => 2
  | .oddCanonical => 1
  | .evenLong => 4
  | .oddLong => 3

def Piece.parity : Piece → Parity
  | .evenCanonical | .evenLong => .even
  | .oddCanonical | .oddLong => .odd

def canonicalPiece : Parity → Piece
  | .even => .evenCanonical
  | .odd => .oddCanonical

/-! ## Canonical finite graph semantics -/

/-- A finite graph whose vertex order is part of the ambient value. -/
abbrev SeriesObject := Σ order : Nat, Graph.FiniteObject (Fin order)

def EvenLength (length : Nat) : Prop := length % 2 = 0

def SeriesHasEvenCycle (object : SeriesObject) : Prop :=
  Graph.HasCycleWithLength object.2.graph EvenLength

def seriesProblem : Core.Problem where
  Ambient := SeriesObject
  Baseline := fun _ => True
  rank := fun object => object.1
  BranchState := fun _ => Unit

local instance (order : Nat) :
    DecidableRel (SimpleGraph.pathGraph order).Adj :=
  Graph.pathGraphAdjDecidable order

def pathObject (edges : Nat) : SeriesObject :=
  ⟨edges + 1, {
    graph := SimpleGraph.pathGraph (edges + 1)
    input := {
      vertices := inferInstance
      decideAdj := Graph.pathGraphAdjDecidable (edges + 1)
    }
  }⟩

/-- `cycleObject offset` is the canonical cycle of length `offset + 3`. -/
def cycleObject (offset : Nat) : SeriesObject :=
  ⟨offset + 3, {
    graph := SimpleGraph.cycleGraph (offset + 3)
    input := {
      vertices := inferInstance
      decideAdj := inferInstance
    }
  }⟩

/-- Canonical series gluing.  The two nonempty return coordinates close a
cycle whose length is the sum of the two path lengths. -/
def glue : Piece → Context → SeriesObject
  | piece, .empty => pathObject piece.length
  | piece, .evenReturn => cycleObject (piece.length + 2 - 3)
  | piece, .oddReturn => cycleObject (piece.length + 3 - 3)
  | _piece, .targetPresent => cycleObject 1

theorem pathObject_piece_hasNoEvenCycle (piece : Piece) :
    ¬ SeriesHasEvenCycle (pathObject piece.length) := by
  rintro ⟨cycle⟩
  cases piece with
  | evenCanonical =>
      exact Graph.pathGraph_three_isAcyclic cycle.walk cycle.isCycle
  | oddCanonical =>
      exact Graph.pathGraph_two_isAcyclic cycle.walk cycle.isCycle
  | evenLong =>
      exact Graph.pathGraph_five_isAcyclic cycle.walk cycle.isCycle
  | oddLong =>
      exact Graph.pathGraph_four_isAcyclic cycle.walk cycle.isCycle

/-- Exact parity theorem for a canonical cycle component. -/
theorem cycleObject_hasEvenCycle_iff (offset : Nat) :
    SeriesHasEvenCycle (cycleObject offset) ↔
      (offset + 3) % 2 = 0 := by
  exact Graph.hasCycleWithLength_cycleGraph_iff EvenLength offset

/-! ## Four exact local response coordinates -/

def response : Piece → Context → Bool
  | _, .empty => false
  | .evenCanonical, .evenReturn | .evenLong, .evenReturn => true
  | .oddCanonical, .evenReturn | .oddLong, .evenReturn => false
  | .evenCanonical, .oddReturn | .evenLong, .oddReturn => false
  | .oddCanonical, .oddReturn | .oddLong, .oddReturn => true
  | _, .targetPresent => true

def storedResponse (row : Row) (context : Context) : Bool :=
  response (canonicalPiece row) context

private theorem response_correct (piece : Piece) (context : Context) :
    response piece context = true ↔ SeriesHasEvenCycle (glue piece context) := by
  cases context with
  | empty =>
      simpa [response, glue] using pathObject_piece_hasNoEvenCycle piece
  | evenReturn =>
      cases piece <;>
        simp [response, glue, Piece.length, cycleObject_hasEvenCycle_iff]
  | oddReturn =>
      cases piece <;>
        simp [response, glue, Piece.length, cycleObject_hasEvenCycle_iff]
  | targetPresent =>
      cases piece <;>
        simp [response, glue, cycleObject_hasEvenCycle_iff]

private theorem contractWorkBound :
    CT3.localCheckBound contexts parities parities ≤ 28 := by
  native_decide

/-- Complete local-coordinate instantiation of the generic CT3 engine. -/
def contract :
    CT3.TargetCompressionContract seriesProblem SeriesHasEvenCycle where
  Piece := Piece
  CompatibleContext := Context
  Coordinate := Context
  Candidate := Candidate
  Row := Row
  glue := glue
  classify := id
  response := response
  response_correct := response_correct
  candidatePiece := canonicalPiece
  AdmissibleReplacement := fun _object _source _candidate => True
  StrictlySmaller := fun _object source candidate =>
    (canonicalPiece candidate).length < source.length
  rowPiece := canonicalPiece
  rowResponse := storedResponse
  coordinates := contexts
  candidates := parities
  rows := parities
  admissibleDecidable := fun _object _source _candidate => .isTrue trivial
  smallerDecidable := fun _object _source _candidate => inferInstance
  inputSize := fun object => object.1
  workCoefficient := 28
  workDegree := 0
  workBound := by
    intro object
    change CT3.localCheckBound contexts parities parities ≤ 28
    exact contractWorkBound

abbrev ct3Spec := contract.spec
abbrev ct3Capability := contract.capability

def ambient : SeriesObject := cycleObject 1

def branch : Core.BranchContext seriesProblem where
  G := ambient
  baseline := trivial
  state := ()

def ct3Input (piece : Piece) : CT3.Input ct3Spec :=
  contract.input branch piece

def run (piece : Piece) := contract.run branch piece

/-- Computed response vector in the declared coordinate order. -/
def responseVector (piece : Piece) : List Bool :=
  contexts.orderedValues.map (response piece)

theorem evenCanonical_response :
    responseVector .evenCanonical = [false, true, false, true] := by
  native_decide

theorem evenLong_response :
    responseVector .evenLong = [false, true, false, true] := by
  native_decide

theorem oddCanonical_response :
    responseVector .oddCanonical = [false, false, true, true] := by
  native_decide

theorem oddLong_response :
    responseVector .oddLong = [false, false, true, true] := by
  native_decide

theorem even_series_sameResponse :
    CT3.SameResponse ct3Spec .evenCanonical .evenLong := by
  intro context
  cases context <;> rfl

theorem odd_series_sameResponse :
    CT3.SameResponse ct3Spec .oddCanonical .oddLong := by
  intro context
  cases context <;> rfl

theorem parity_rows_distinct :
    ¬ CT3.SameResponse ct3Spec .evenCanonical .oddCanonical := by
  intro same
  have differs := same Context.evenReturn
  contradiction

def evenLongRun := run .evenLong
def oddLongRun := run .oddLong
def evenCanonicalRun := run .evenCanonical
def oddCanonicalRun := run .oddCanonical

theorem evenLong_terminal : evenLongRun.terminal = .compression := by
  native_decide

theorem oddLong_terminal : oddLongRun.terminal = .compression := by
  native_decide

theorem evenCanonical_terminal : evenCanonicalRun.terminal = .knownRow := by
  native_decide

theorem oddCanonical_terminal : oddCanonicalRun.terminal = .knownRow := by
  native_decide

theorem evenLong_trace : evenLongRun.trace =
    [.entry, .vectorComputation, .compressionSearch,
      .compressionTerminal] := by
  native_decide

theorem oddCanonical_trace : oddCanonicalRun.trace =
    [.entry, .vectorComputation, .compressionSearch,
      .tableValidation, .rowLookup, .knownRowTerminal] := by
  native_decide

theorem run_checkLimit (piece : Piece) : (run piece).checkLimit = 28 := by
  cases piece <;> native_decide

theorem run_checkLimit_polynomial (piece : Piece) :
    (run piece).checkLimit ≤ contract.workCoefficient *
      (contract.inputSize branch.G + 1) ^ contract.workDegree :=
  contract.run_checkLimit_polynomial branch piece

theorem sameResponse_preserves_target
    {left right : Piece}
    (same : CT3.SameResponse ct3Spec left right) (context : Context) :
    SeriesHasEvenCycle (glue left context) ↔
      SeriesHasEvenCycle (glue right context) :=
  contract.sameResponse_target_iff same context

theorem run_verified (piece : Piece) :
    CT3.OutcomeClaim (run piece).outcome :=
  contract.run_verified branch piece

theorem run_traceValid (piece : Piece) :
    @CT3.Graph.ValidTrace seriesProblem ct3Spec ct3Capability
      (ct3Input piece) (run piece).trace :=
  contract.run_traceValid branch piece

theorem run_total (piece : Piece) :
    ∃ result : CT3.ExecutionResult ct3Spec ct3Capability (ct3Input piece),
      CT3.OutcomeClaim result.outcome ∧
        @CT3.Graph.ValidTrace seriesProblem ct3Spec ct3Capability
          (ct3Input piece) result.trace :=
  contract.run_total branch piece

/-! ## Transfer of the literal packed-graph replacement profile -/

/-- The same even-cycle length predicate instantiated in the reusable packed
minimum-degree graph problem.  Threshold zero supplies a harmless finite
target-avoiding seed for the independent CT3 transfer audit. -/
def concretePackedInput : Graph.PackedMinimumDegreeCycle.StaticInput where
  minimumDegree := 0
  LengthOK := EvenLength

private def concreteSeedObject : Graph.PackedFiniteObject :=
  Graph.PackedFiniteObject.pack (pathObject Piece.oddCanonical.length).2

private theorem concreteSeed_avoids :
    ¬ concretePackedInput.Target concreteSeedObject := by
  simpa [concreteSeedObject, concretePackedInput,
    Graph.PackedMinimumDegreeCycle.StaticInput.Target,
    Graph.PackedFiniteObject.pack, SeriesHasEvenCycle, Piece.length] using
      pathObject_piece_hasNoEvenCycle Piece.oddCanonical

private def concreteAvoidingContext :
    Core.AvoidingContext concretePackedInput.problem concretePackedInput.Target :=
  Core.AvoidingContext.ofBranch {
    G := concreteSeedObject
    baseline := Nat.zero_le _
    state := ()
  } concreteSeed_avoids

/-- Independent textbook transfer: the even-cycle package constructs the
exact literal-gluing CT3 stage used by the Erdős implementation. -/
theorem exists_duffinConcreteBoundariedReplacementStage :
    ∃ ctx : Core.MinimalCounterexampleContext
        concretePackedInput.problem concretePackedInput.Target,
      concretePackedInput.problem.rank ctx.G ≤
          concretePackedInput.problem.rank concreteSeedObject ∧
        Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.VerifiedStage
          concretePackedInput (inferInstance : FinEnum (Fin 2)) ctx := by
  obtain ⟨ctx, rankLe⟩ :=
    concreteAvoidingContext.exists_minimalCounterexample (fun _object => ())
  exact ⟨ctx, rankLe,
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
      concretePackedInput (inferInstance : FinEnum (Fin 2)) ctx⟩

end EvenCycleExample.SeriesReduction
