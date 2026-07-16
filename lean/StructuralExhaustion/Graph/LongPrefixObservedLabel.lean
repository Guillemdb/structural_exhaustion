import StructuralExhaustion.Core.FiniteCodeCollision
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.LongPrefixObservedLabel

open StructuralExhaustion

universe u

/-!
# Observed local labels on a long graph-owned support

This profile deliberately stops before CT8.  It labels literal entries of one
supplied support by two graph-derived coordinates: ambient degree modulo four
and membership in one supplied local marked set.  Thus the label alphabet has
eight values.  The runner inspects only the first nine observed entries and
returns an actual ordered collision.  It never enumerates the label universe,
the ambient graph universe, paths, subsets, or Boolean functions.

Equality of these coarse labels is not response equivalence and does not
authorize removal.  The result is therefore a semantic-refinement residual.
-/

/-- One graph-owned support and a local marked vertex set. -/
structure Input {V : Type u} (object : FiniteObject V) where
  support : List V
  marked : Finset V
  firstNine : 9 ≤ support.length

/-- The bounded observed schedule used by the executable collision scan. -/
abbrev Occurrence := Fin 9

/-- Exact graph-derived coarse label. -/
abbrev Label := Fin 4 × Bool

@[implicit_reducible]
def labels : FinEnum Label :=
  Core.Enumeration.prod (by infer_instance) Core.Enumeration.bool

@[simp]
theorem labels_card : labels.card = 8 := by
  rw [@FinEnum.card_eq_fintypeCard Label labels inferInstance]
  norm_num

@[implicit_reducible]
def occurrences : FinEnum Occurrence := by infer_instance

@[simp]
theorem occurrences_card : occurrences.card = 9 := by
  exact @FinEnum.card_fin 9 occurrences

variable {V : Type u} {object : FiniteObject V}

/-- Embed one of the first nine observations into the literal support. -/
def supportPosition (input : Input object) (occurrence : Occurrence) :
    Fin input.support.length :=
  ⟨occurrence.1, lt_of_lt_of_le occurrence.2 input.firstNine⟩

/-- Literal support entry at an observed position. -/
def vertex (input : Input object) (occurrence : Occurrence) : V :=
  input.support.get (supportPosition input occurrence)

/-- Ambient degree reduced to one of four exact residues. -/
def degreeResidue (input : Input object) (occurrence : Occurrence) : Fin 4 :=
  ⟨object.degree (vertex input occurrence) % 4, Nat.mod_lt _ (by decide)⟩

/-- The exact local marked-set membership bit. -/
noncomputable def markedBit (input : Input object) (occurrence : Occurrence) : Bool := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact decide (vertex input occurrence ∈ input.marked)

/-- Coarse observed code computed from the selected graph and support entry. -/
noncomputable def label (input : Input object) (occurrence : Occurrence) : Label :=
  (degreeResidue input occurrence, markedBit input occurrence)

/-- The executable schedule consists of the first nine literal positions in
their inherited order. -/
def schedule : List Occurrence := occurrences.orderedValues

@[simp]
theorem schedule_length : schedule.length = 9 := by
  rw [schedule, FinEnum.orderedValues_length, occurrences_card]

theorem schedule_nodup : schedule.Nodup := occurrences.nodup_orderedValues

/-- Exact repeated observed label, retaining both literal positions. -/
structure Repetition (input : Input object) where
  collision : Core.FiniteCodeCollision.OrderedCollision (label input) schedule
  distinct : collision.first ≠ collision.second
  sameLabel : label input collision.first = label input collision.second
  decisionExact : Core.FiniteCodeCollision.decideWithDecEq
    (label input) schedule = .collision collision

/-- The honest frontier produced before compatible response contexts and a
certified removal have been constructed. -/
structure SemanticRefinementResidual (input : Input object) where
  repetition : Repetition input

/-- Deterministic first-collision scan over nine observed codes.  The
impossible unique branch is discharged only by the proof-level alphabet
cardinality; `decideWithDecEq` does not enumerate that alphabet. -/
noncomputable def run (input : Input object) : SemanticRefinementResidual input := by
  classical
  cases decision : Core.FiniteCodeCollision.decideWithDecEq
      (label input) schedule with
  | collision collision =>
      exact ⟨⟨collision,
        collision.first_ne_second_of_nodup schedule_nodup,
        collision.code_eq, decision⟩⟩
  | unique codesNodup =>
      have collision := Core.FiniteCodeCollision.collision_of_card_lt_length
        labels (label input) schedule (by simp)
      exact (collision.some.false_of_codes_nodup codesNodup).elim

theorem run_distinct (input : Input object) :
    (run input).repetition.collision.first ≠
      (run input).repetition.collision.second :=
  (run input).repetition.distinct

theorem run_sameLabel (input : Input object) :
    label input (run input).repetition.collision.first =
      label input (run input).repetition.collision.second :=
  (run input).repetition.sameLabel

theorem run_first_mem (input : Input object) :
    (run input).repetition.collision.first ∈ schedule :=
  (run input).repetition.collision.first_mem

theorem run_second_mem (input : Input object) :
    (run input).repetition.collision.second ∈ schedule :=
  (run input).repetition.collision.second_mem

theorem run_decision_exact (input : Input object) :
    Core.FiniteCodeCollision.decideWithDecEq (label input) schedule =
      .collision (run input).repetition.collision :=
  (run input).repetition.decisionExact

/-- Visible equality/membership work bound.  At most 36 label pairs are
compared.  The uncached equality test evaluates two labels per pair; each
label evaluation scans at most the declared vertex order for degree and the
supplied marked set for membership. -/
def visibleChecks (input : Input object) : Nat :=
  72 * (object.input.vertices.card + input.marked.card + 1)

/-- Since the marked set is a set of vertices of the same finite type, the
visible work is linear in the supplied graph size with a fixed constant. -/
theorem visibleChecks_le (input : Input object) :
    visibleChecks input ≤ 144 * (object.input.vertices.card + 1) := by
  letI : DecidableEq V := object.input.vertices.decEq
  have markedLe : input.marked.card ≤ object.input.vertices.card := by
    rw [← object.card_vertexFinset]
    exact Finset.card_le_card (by intro vertex _; exact object.mem_vertexFinset vertex)
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.LongPrefixObservedLabel
