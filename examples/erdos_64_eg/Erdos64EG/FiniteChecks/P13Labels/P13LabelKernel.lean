import Erdos64EG.InternalProblem
import StructuralExhaustion.Graph.InducedPathAttachment

namespace Erdos64EG.Internal.P13LabelKernel

open StructuralExhaustion

/-!
# Fixed `P₁₃` label computation kernel

This module contains only the definitions needed by the fixed finite
attachment-label computation.  It deliberately does not import any Erdős
proof stage after `InternalProblem`, so changes to CT1, CT2, CT3, CT12, or the
CT10 graph integration do not invalidate the cached computation module.
-/

/-- One attachment set on the thirteen labelled path positions. -/
abbrev Label := Graph.InducedPathAttachment.Label 13

/-- Compact thirteen-bit representation of an attachment set. -/
abbrev Code := BitVec 13

/-- Constant-width bit-vector form of the manuscript gap rule. -/
def CodeLegal (code : Code) : Prop :=
  code ≠ 0#13 ∧
    code &&& (code >>> 2) = 0#13 ∧
    code &&& (code >>> 6) = 0#13

def codeLegalDecidable (code : Code) : Decidable (CodeLegal code) := by
  unfold CodeLegal
  infer_instance

/-- Boolean exposed by the exact code-legality decision procedure. -/
def codeLegalBool (code : Code) : Bool :=
  @decide (CodeLegal code) (codeLegalDecidable code)

/-- Sequential enumeration of the fixed `2¹³` code universe. -/
@[implicit_reducible]
def codes : FinEnum Code :=
  Graph.InducedPathAttachment.labelCodes 13

/-- Exact CT10 profile over the fixed code universe. -/
def classification : CT10.ExhaustiveClassification.Profile Code where
  candidates := codes
  Accepts := CodeLegal
  acceptsDecidable := codeLegalDecidable

/-- Number of legal codes with a prescribed population count. -/
def labelsOfSize (size : Nat) : Nat :=
  (codes.orderedValues.filter fun code =>
    @decide (CodeLegal code) (codeLegalDecidable code) &&
      decide (code.cpop.toNat = size)).length

end Erdos64EG.Internal.P13LabelKernel
