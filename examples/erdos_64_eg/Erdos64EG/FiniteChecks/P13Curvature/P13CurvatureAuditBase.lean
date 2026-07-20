import Erdos64EG.Shared.SurplusScaleSplit
import Erdos64EG.FiniteChecks.P13Curvature.P13CurvatureCertificate
import Erdos64EG.FiniteChecks.P13Curvature.P13CurvatureArithmeticCertificate
import Erdos64EG.FiniteChecks.P13Curvature.P13CurvatureAscendingCarrier

namespace Erdos64EG.Internal

open StructuralExhaustion

def p13CurvatureCodes : Array P13LabelCode :=
  p13AscendingCodes

/-- Explicit yellow input retaining exactly the already proved carrier output
needed while its old monolithic implementation is replaced.  The input is a
typed consequence, not an axiom and not green evidence: it supplies the
canonical CT10 legal label at each of the `399` shallow positions and the
pointwise code alignment.  No mention of the ambient `8192`-code filter enters
the optimized dependency cone. -/
structure P13CurvatureLegacyCarrierInput : Type where
  labelEquiv : Fin 399 ≃ LegalP13Label
  code_eq : ∀ index, (labelEquiv index).1 = p13AscendingCode index

/-- Canonical legal label at one shallow carrier position. -/
def p13AscendingLegalLabelAt
    (legacy : P13CurvatureLegacyCarrierInput) (index : Fin 399) :
    LegalP13Label :=
  legacy.labelEquiv index

/-- Pointwise alignment supplied by the explicitly yellow old-output input. -/
theorem p13AscendingLegalLabelAt_code
    (legacy : P13CurvatureLegacyCarrierInput) (index : Fin 399) :
    (p13AscendingLegalLabelAt legacy index).1 = p13AscendingCode index :=
  legacy.code_eq index

/-- The ascending schedule is therefore an exact legal-label carrier, with
legality inherited from the CT10 subtype rather than recomputed per code. -/
theorem p13AscendingCode_legal
    (legacy : P13CurvatureLegacyCarrierInput) (index : Fin 399) :
    P13CodeLegal (p13AscendingCode index) := by
  rw [← p13AscendingLegalLabelAt_code legacy index]
  exact (p13AscendingLegalLabelAt legacy index).2

def p13CurvatureLabel (index : Fin 399) : P13Label :=
  p13LabelEquiv (p13AscendingCode index)

def P13CodeCompatible (shift : Nat) (left right : P13LabelCode) : Prop :=
  ∀ leftPosition rightPosition : Fin 13,
    left.getLsb leftPosition = true →
      right.getLsb rightPosition = true →
        ¬PowerOfTwoLength
          (Graph.InducedPathAttachment.crossCycleLength
            shift leftPosition rightPosition)

def p13CodeCompatibleDecidable (shift : Nat) (left right : P13LabelCode) :
    Decidable (P13CodeCompatible shift left right) := by
  unfold P13CodeCompatible
  infer_instance

def P13CodeCompatibleOne (left right : P13LabelCode) : Prop :=
  left &&& (right >>> 1) = 0#13 ∧
    right &&& (left >>> 1) = 0#13 ∧
    left &&& (right >>> 5) = 0#13 ∧
    right &&& (left >>> 5) = 0#13

def P13CodeCompatibleTwo (left right : P13LabelCode) : Prop :=
  left &&& right = 0#13 ∧
    left &&& (right >>> 4) = 0#13 ∧
    right &&& (left >>> 4) = 0#13 ∧
    left &&& (right >>> 12) = 0#13 ∧
    right &&& (left >>> 12) = 0#13

def p13CodeCompatibleOneDecidable (left right : P13LabelCode) :
    Decidable (P13CodeCompatibleOne left right) := by
  unfold P13CodeCompatibleOne
  infer_instance

def p13CodeCompatibleTwoDecidable (left right : P13LabelCode) :
    Decidable (P13CodeCompatibleTwo left right) := by
  unfold P13CodeCompatibleTwo
  infer_instance

abbrev p13CompatibilityRowsOne := P13CurvatureCertificate.rowsOne
abbrev p13CompatibilityRowsTwo := P13CurvatureCertificate.rowsTwo

end Erdos64EG.Internal
