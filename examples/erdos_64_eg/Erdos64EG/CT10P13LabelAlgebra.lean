import Erdos64EG.CT12InducedP13Packing
import Erdos64EG.P13LabelCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT10: the finite `P₁₃` attachment-label algebra

This stage implements manuscript node `[18]`.  A label is a nonempty subset
of the thirteen path positions.  Target avoidance permits exactly those
labels whose pairwise position gaps are neither `2` nor `6`; the reusable
graph layer proves this by constructing the resulting length-`4` or
length-`8` cycle.  CT10 audits the complete finite legal-label table.

The scale relations `C_s` and the two-step indicator `Ω₂` are defined here as
the fixed Erdős instantiation of the reusable path-attachment algebra.  Their
later aggregate curvature enumeration belongs to the downstream curvature
stage.
-/

private theorem thirteen_positive : 0 < 13 := by decide

/-- Explicit decision procedure supplied to the reusable graph/profile
boundary. -/
def decidePowerOfTwoLength (length : Nat) :
    Decidable (PowerOfTwoLength length) :=
  powerOfTwoLengthDecidable length

/-- One possible attachment set on the labelled path
`v₀,…,v₁₂`. -/
abbrev P13Label := Graph.InducedPathAttachment.Label 13

/-- Compact thirteen-bit representation used by the executable table. -/
abbrev P13LabelCode := P13LabelKernel.Code

/-- Decode a compact label code to the corresponding set of positions. -/
abbrev decodeP13Label (code : P13LabelCode) : P13Label :=
  Graph.InducedPathAttachment.decodeCode code

/-- Encode a set of positions as a thirteen-bit label. -/
abbrev encodeP13Label (label : P13Label) : P13LabelCode :=
  Graph.InducedPathAttachment.encodeLabel label

/-- Exact executable equivalence between bit codes and finite position
sets. -/
abbrev p13LabelEquiv : P13LabelCode ≃ P13Label :=
  Graph.InducedPathAttachment.labelCodeEquiv 13

@[simp] theorem p13LabelEquiv_apply (code : P13LabelCode) :
    p13LabelEquiv code = decodeP13Label code :=
  rfl

/-- The manuscript legality predicate. -/
abbrev P13Legal (label : P13Label) : Prop :=
  Graph.InducedPathAttachment.Legal 13 PowerOfTwoLength label

/-- Pairwise-gap form printed in the manuscript. -/
def P13GapLegal (label : P13Label) : Prop :=
  label.Nonempty ∧
    ∀ left ∈ label, ∀ right ∈ label, left < right →
      right.1 - left.1 ≠ 2 ∧ right.1 - left.1 ≠ 6

/-- On thirteen positions, an accepted power-of-two pair cycle is exactly a
gap of `2` or `6`, producing cycle length `4` or `8`. -/
theorem pairCycleLength_powerOfTwo_iff_gap_two_or_six
    (left right : Fin 13) (left_lt_right : left < right) :
    PowerOfTwoLength
        (Graph.InducedPathAttachment.pairCycleLength left right) ↔
      right.1 - left.1 = 2 ∨ right.1 - left.1 = 6 :=
  P13LabelCertificate.pairCycleLength_powerOfTwo_iff_gap_two_or_six
    left right left_lt_right

/-- The executable graph-level legality predicate is exactly the prose
gap-avoidance rule. -/
theorem p13Legal_iff_gapLegal (label : P13Label) :
    P13Legal label ↔ P13GapLegal label := by
  constructor
  · rintro ⟨nonempty, safe⟩
    refine ⟨nonempty, ?_⟩
    intro left leftMember right rightMember left_lt_right
    have notPower := safe left leftMember right rightMember left_lt_right
    rw [pairCycleLength_powerOfTwo_iff_gap_two_or_six left right
      left_lt_right] at notPower
    exact not_or.mp notPower
  · rintro ⟨nonempty, safe⟩
    refine ⟨nonempty, ?_⟩
    intro left leftMember right rightMember left_lt_right
    rw [pairCycleLength_powerOfTwo_iff_gap_two_or_six left right
      left_lt_right]
    exact not_or.mpr (safe left leftMember right rightMember left_lt_right)

/-- Constant-time arithmetic decision kernel for one candidate label. -/
def p13GapLegalDecidable (label : P13Label) :
    Decidable (P13GapLegal label) := by
  unfold P13GapLegal
  infer_instance

/-- Constant-work bit-vector form of the gap rule. -/
abbrev P13CodeLegal := P13LabelKernel.CodeLegal

def p13CodeLegalDecidable (code : P13LabelCode) :
    Decidable (P13CodeLegal code) :=
  P13LabelKernel.codeLegalDecidable code

/-- Boolean exposed by the exact code-legality decision procedure. -/
def p13CodeLegalBool (code : P13LabelCode) : Bool :=
  P13LabelKernel.codeLegalBool code

/-- Sequential enumeration of the `2¹³` compact label codes. -/
@[implicit_reducible]
def p13LabelCodes : FinEnum P13LabelCode :=
  P13LabelKernel.codes

/-- The bit-vector kernel recognizes exactly the manuscript's finite-set
gap predicate. -/
theorem p13CodeLegal_iff_gapLegal (code : P13LabelCode) :
    P13CodeLegal code ↔ P13GapLegal (p13LabelEquiv code) := by
  rw [p13LabelEquiv_apply]
  have gapTwo :=
    Graph.InducedPathAttachment.and_shift_eq_zero_iff_no_gap code 2 (by omega)
  have gapSix :=
    Graph.InducedPathAttachment.and_shift_eq_zero_iff_no_gap code 6 (by omega)
  constructor
  · rintro ⟨nonzero, noTwo, noSix⟩
    refine ⟨?_, ?_⟩
    · exact
        (Graph.InducedPathAttachment.decodeCode_nonempty_iff code).2 nonzero
    · intro left leftMember right rightMember left_lt_right
      exact ⟨gapTwo.1 noTwo left leftMember right rightMember left_lt_right,
        gapSix.1 noSix left leftMember right rightMember left_lt_right⟩
  · rintro ⟨nonempty, safe⟩
    refine ⟨?_, ?_, ?_⟩
    · exact
        (Graph.InducedPathAttachment.decodeCode_nonempty_iff code).1 nonempty
    · apply gapTwo.2
      intro left leftMember right rightMember left_lt_right
      exact (safe left leftMember right rightMember left_lt_right).1
    · apply gapSix.2
      intro left leftMember right rightMember left_lt_right
      exact (safe left leftMember right rightMember left_lt_right).2

/-- Exact CT10 profile using the manuscript's gap normal form. -/
def p13LabelClassification :
    CT10.ExhaustiveClassification.Profile P13LabelCode :=
  P13LabelKernel.classification

/-- Proof that the optimized local table classifies exactly the graph-level
legal attachment labels. -/
def p13AttachmentClassification :
    Graph.InducedPathAttachment.Classification 13 PowerOfTwoLength where
  Candidate := P13LabelCode
  profile := p13LabelClassification
  decode := p13LabelEquiv
  accepts_iff_legal := fun code =>
    (p13CodeLegal_iff_gapLegal code).trans
      (p13Legal_iff_gapLegal (p13LabelEquiv code)).symm

/-- A legal attachment label, with its gap-legality proof carried in the
finite class type. -/
abbrev LegalP13Label := p13LabelClassification.Class

/-! ## Exact finite table -/

/-- Population count is exactly the cardinality of the decoded label.  This
fixed-width check concerns only the thirteen code coordinates. -/
theorem p13LabelCode_card (code : P13LabelCode) :
    (p13LabelEquiv code).card = code.cpop.toNat :=
  P13LabelCertificate.labelCode_card code

/-- Number of legal labels of a fixed cardinality. -/
def p13LabelsOfSize (size : Nat) : Nat :=
  P13LabelKernel.labelsOfSize size

/-- One proof-producing local computation certifies the table cardinality
and all seven size fibres. -/
theorem p13Label_table_computation :
    p13LabelClassification.classCount = 399 ∧
      (p13LabelsOfSize 1 = 13 ∧
       p13LabelsOfSize 2 = 60 ∧
       p13LabelsOfSize 3 = 122 ∧
       p13LabelsOfSize 4 = 122 ∧
       p13LabelsOfSize 5 = 63 ∧
       p13LabelsOfSize 6 = 17 ∧
       p13LabelsOfSize 7 = 2) :=
  P13LabelCertificate.table_computation



/-- The complete legal-label table has the manuscript's `399` rows. -/
theorem p13LegalLabel_count :
    p13LabelClassification.classCount = 399 :=
  p13Label_table_computation.1

/-- Exact size distribution `(13,60,122,122,63,17,2)` for label sizes
`1,…,7`. -/
theorem p13LegalLabel_size_distribution :
    p13LabelsOfSize 1 = 13 ∧
    p13LabelsOfSize 2 = 60 ∧
    p13LabelsOfSize 3 = 122 ∧
    p13LabelsOfSize 4 = 122 ∧
    p13LabelsOfSize 5 = 63 ∧
    p13LabelsOfSize 6 = 17 ∧
    p13LabelsOfSize 7 = 2 :=
  p13Label_table_computation.2

/-- Closed bounded computation behind the maximum-label-size certificate. -/
private theorem p13LegalCode_card_bounds_computation :
    ∀ code : P13LabelCode, p13CodeLegalBool code = true →
      1 ≤ code.cpop.toNat ∧ code.cpop.toNat ≤ 7 :=
  P13LabelCertificate.legalCode_card_bounds_computation

/-- The compact legality kernel also certifies the manuscript's maximum
label size. -/
theorem p13LegalCode_card_bounds (code : P13LabelCode)
    (legal : P13CodeLegal code) :
    1 ≤ code.cpop.toNat ∧ code.cpop.toNat ≤ 7 := by
  apply p13LegalCode_card_bounds_computation code
  simp [p13CodeLegalBool, P13LabelKernel.codeLegalBool, legal]

/-- Every legal label has one of the seven sizes listed above. -/
theorem legalP13Label_card_bounds (label : LegalP13Label) :
    1 ≤ (p13LabelEquiv label.1).card ∧
      (p13LabelEquiv label.1).card ≤ 7 := by
  rw [p13LabelCode_card]
  exact p13LegalCode_card_bounds label.1 label.2

/-- The source universe is only the `2¹³` subsets of the fixed path
positions. -/
theorem p13Label_candidate_count :
    p13LabelClassification.candidateCount = 8192 :=
  P13LabelCertificate.candidate_count

/-- Exact local predicate-check ledger for the CT10 table audit. -/
theorem p13Label_check_count :
    p13LabelClassification.checks = 167792 := by
  rw [CT10.ExhaustiveClassification.Profile.checks,
    p13Label_candidate_count, p13LegalLabel_count]
  norm_num

/-- The complete fixed table audit obeys the generic quadratic candidate
bound. -/
theorem p13Label_checks_quadratic :
    p13LabelClassification.checks ≤
      (p13LabelClassification.candidateCount + 1) ^ 2 := by
  rw [p13Label_check_count, p13Label_candidate_count]
  norm_num

/-! ## Exact CT10 execution -/

/-- CT10 input inherits the selected minimal graph's branch context and
contains the complete legal-label table. -/
def p13LabelCT10Input
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  p13LabelClassification.input ctx.toBranchContext

/-- Execute CT10 on the legal-label table. -/
def runP13LabelCT10
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  p13LabelClassification.run ctx.toBranchContext

/-- Complete reusable verification package for this CT10 execution. -/
def verifiedP13LabelCT10Stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13LabelClassification.VerifiedStage ctx.toBranchContext :=
  p13LabelClassification.verifiedStage ctx.toBranchContext

theorem runP13LabelCT10_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runP13LabelCT10 ctx).terminal = .exhaustive :=
  (verifiedP13LabelCT10Stage ctx).terminal

theorem runP13LabelCT10_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runP13LabelCT10 ctx).trace =
      [.entry, .table, .direct, .missing, .exhaustiveTerminal] :=
  (verifiedP13LabelCT10Stage ctx).trace

theorem runP13LabelCT10_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ∃ result : CT10.ExecutionResult
        (p13LabelClassification.capability PackedProblem.{u})
        (p13LabelCT10Input ctx),
      result.terminal = .exhaustive ∧
        result.trace =
          [.entry, .table, .direct, .missing, .exhaustiveTerminal] ∧
        result.outcome.Valid ∧
        CT10.Graph.ValidTrace
          (p13LabelClassification.capability PackedProblem.{u})
          (p13LabelCT10Input ctx) result.trace :=
  (verifiedP13LabelCT10Stage ctx).total


/-! ## Manuscript relations `C_s` and `Ω₂` -/

/-- Erdős specialization of the zero-one compatibility coefficient. -/
def p13C (shift : Nat) (left right : P13Label) : Nat :=
  Graph.InducedPathAttachment.C 13 PowerOfTwoLength
    decidePowerOfTwoLength shift left right

/-- Erdős specialization of the two-step curvature indicator. -/
def p13OmegaTwo (source middle target : P13Label) : Nat :=
  Graph.InducedPathAttachment.omegaTwo 13 PowerOfTwoLength
    decidePowerOfTwoLength source middle target

theorem p13C_eq_one_iff (shift : Nat) (left right : P13Label) :
    p13C shift left right = 1 ↔
      Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength shift
        left right :=
  Graph.InducedPathAttachment.C_eq_one_iff 13 PowerOfTwoLength
    decidePowerOfTwoLength shift left right

theorem p13OmegaTwo_eq_one_iff (source middle target : P13Label) :
    p13OmegaTwo source middle target = 1 ↔
      Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength 1
          source middle ∧
        Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength 1
          middle target ∧
        ¬Graph.InducedPathAttachment.Compatible 13 PowerOfTwoLength 2
          source target :=
  Graph.InducedPathAttachment.omegaTwo_eq_one_iff 13 PowerOfTwoLength
    decidePowerOfTwoLength source middle target

/-! ## Fully connected verified prefix -/

/-- Generic graph/framework CT10 extension of the exact CT12 prefix. -/
abbrev GenericP13LabelAlgebraPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  packedStaticInput.InducedPathPackingAttachmentPrefix 13 thirteen_positive
      p13AttachmentClassification ctx

/-- Exact output of node `[18]`, retaining every previous proof stage. -/
structure VerifiedP13LabelAlgebraPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedP13PackingPrefix ctx
  generic : GenericP13LabelAlgebraPrefix ctx
  samePacking : generic.previous = previous.generic
  labelCount : p13LabelClassification.classCount = 399
  sizeDistribution :
    p13LabelsOfSize 1 = 13 ∧ p13LabelsOfSize 2 = 60 ∧
    p13LabelsOfSize 3 = 122 ∧ p13LabelsOfSize 4 = 122 ∧
    p13LabelsOfSize 5 = 63 ∧ p13LabelsOfSize 6 = 17 ∧
    p13LabelsOfSize 7 = 2

/-- Extend the exact CT12 output through node `[18]` on the identical
selected minimal graph. -/
noncomputable def verifiedP13LabelAlgebraPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PackingPrefix ctx) :
    VerifiedP13LabelAlgebraPrefix ctx where
  previous := previous
  generic :=
    packedStaticInput.inducedPathPackingAttachmentPrefix
      13 thirteen_positive p13AttachmentClassification ctx previous.generic
  samePacking := rfl
  labelCount := p13LegalLabel_count
  sizeDistribution := p13LegalLabel_size_distribution

/-- The new CT10 stage consumes the exact preceding CT12 output. -/
theorem p13LabelAlgebraPrefix_previous
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedP13LabelAlgebraPrefix ctx) :
    VerifiedP13PackingPrefix ctx :=
  verified.previous

/-- Complete CT10 exhaustive-classification stage retained in the prefix. -/
theorem p13LabelAlgebraPrefix_stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedP13LabelAlgebraPrefix ctx) :
    p13LabelClassification.VerifiedStage ctx.toBranchContext :=
  verified.generic.classificationStage

/-- Every actual nonempty attachment label on any induced `P₁₃` in the
selected target-avoiding graph is one of the legal classes. -/
theorem p13AttachmentLabel_legal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedP13LabelAlgebraPrefix ctx)
    (path : SimpleGraph.pathGraph 13 ↪g ctx.G.object.graph)
    (outside : ctx.G.Vertex)
    (outsidePath : ∀ position : Fin 13, outside ≠ path position)
    (attached : ∃ position, ctx.G.object.graph.Adj outside (path position)) :
    P13Legal
      (packedStaticInput.inducedPathAttachmentLabel 13 ctx path outside) :=
  verified.generic.actualLabelsLegal path outside outsidePath attached

/-- The same actual attachment is represented by an accepted row of the
compact CT10 table. -/
theorem p13AttachmentLabel_accepted
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedP13LabelAlgebraPrefix ctx)
    (path : SimpleGraph.pathGraph 13 ↪g ctx.G.object.graph)
    (outside : ctx.G.Vertex)
    (outsidePath : ∀ position : Fin 13, outside ≠ path position)
    (attached : ∃ position, ctx.G.object.graph.Adj outside (path position)) :
    p13LabelClassification.Accepts
      (p13LabelEquiv.symm
        (packedStaticInput.inducedPathAttachmentLabel 13 ctx path outside)) :=
  verified.generic.actualLabelsAccepted path outside outsidePath attached

/-- Starting from the official internal counterexample data, retain one
selected graph and the entire proof through node `[18]`. -/
theorem exists_verifiedP13LabelAlgebraPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedP13LabelAlgebraPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedP13PackingPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedP13LabelAlgebraPrefix ctx previous⟩

end Erdos64EG.Internal
