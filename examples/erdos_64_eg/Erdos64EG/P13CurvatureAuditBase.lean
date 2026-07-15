import Erdos64EG.SurplusScaleSplit
import Erdos64EG.P13CurvatureCertificate
import Erdos64EG.P13CurvatureArithmeticCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion

def p13CurvatureCodes : Array P13LabelCode :=
  (p13LabelClassification.classes.orderedValues.map Subtype.val).toArray

def p13CurvatureLabel (index : Fin 399) : P13Label :=
  p13LabelEquiv (p13CurvatureCodes.getD index.1 0#13)

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
