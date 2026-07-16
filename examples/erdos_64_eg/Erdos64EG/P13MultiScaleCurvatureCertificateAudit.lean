import Erdos64EG.P13MultiScaleCurvatureAudit00
import Erdos64EG.P13MultiScaleCurvatureAudit01
import Erdos64EG.P13MultiScaleCurvatureAudit02
import Erdos64EG.P13MultiScaleCurvatureAudit03
import Erdos64EG.P13MultiScaleCurvatureAudit04
import Erdos64EG.P13MultiScaleCurvatureAudit05
import Erdos64EG.P13MultiScaleCurvatureAudit06
import Erdos64EG.P13MultiScaleCurvatureAudit07
import Erdos64EG.P13MultiScaleCurvatureAudit08
import Erdos64EG.P13MultiScaleCurvatureAudit09
import Erdos64EG.P13MultiScaleCurvatureAudit10
import Erdos64EG.P13MultiScaleCurvatureAudit11
import Erdos64EG.P13MultiScaleCurvatureAudit12
import Erdos64EG.P13MultiScaleCurvatureAudit13
import Erdos64EG.P13MultiScaleCurvatureAudit14

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

theorem p13MultiScaleRows_codeAudit (length : Fin 15)
    (source target : Fin 399) :
    (row length.1 source).getLsb target =
      @decide (P13CodeCompatibleSparse length.1
        (p13CurvatureCodes.getD source.1 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleSparseDecidable length.1 _ _) := by
  fin_cases length
  · exact p13MultiScaleRows_codeAudit_00 source target
  · exact p13MultiScaleRows_codeAudit_01 source target
  · exact p13MultiScaleRows_codeAudit_02 source target
  · exact p13MultiScaleRows_codeAudit_03 source target
  · exact p13MultiScaleRows_codeAudit_04 source target
  · exact p13MultiScaleRows_codeAudit_05 source target
  · exact p13MultiScaleRows_codeAudit_06 source target
  · exact p13MultiScaleRows_codeAudit_07 source target
  · exact p13MultiScaleRows_codeAudit_08 source target
  · exact p13MultiScaleRows_codeAudit_09 source target
  · exact p13MultiScaleRows_codeAudit_10 source target
  · exact p13MultiScaleRows_codeAudit_11 source target
  · exact p13MultiScaleRows_codeAudit_12 source target
  · exact p13MultiScaleRows_codeAudit_13 source target
  · exact p13MultiScaleRows_codeAudit_14 source target

theorem p13MultiScaleSafeCounts_audit (left right : Fin 15) :
    if 0 < left.1 ∧ 0 < right.1 ∧ left.1 + right.1 ≤ 14 then
      safeCount left.1 right.1 = profile.safeCount left.1 right.1
    else safeCount left.1 right.1 = 0 := by
  fin_cases left
  · exact p13MultiScaleSafeCounts_audit_00 right
  · exact p13MultiScaleSafeCounts_audit_01 right
  · exact p13MultiScaleSafeCounts_audit_02 right
  · exact p13MultiScaleSafeCounts_audit_03 right
  · exact p13MultiScaleSafeCounts_audit_04 right
  · exact p13MultiScaleSafeCounts_audit_05 right
  · exact p13MultiScaleSafeCounts_audit_06 right
  · exact p13MultiScaleSafeCounts_audit_07 right
  · exact p13MultiScaleSafeCounts_audit_08 right
  · exact p13MultiScaleSafeCounts_audit_09 right
  · exact p13MultiScaleSafeCounts_audit_10 right
  · exact p13MultiScaleSafeCounts_audit_11 right
  · exact p13MultiScaleSafeCounts_audit_12 right
  · exact p13MultiScaleSafeCounts_audit_13 right
  · exact p13MultiScaleSafeCounts_audit_14 right

theorem p13MultiScaleFlatCounts_audit (left right : Fin 15) :
    if 0 < left.1 ∧ 0 < right.1 ∧ left.1 + right.1 ≤ 14 then
      flatCount left.1 right.1 = profile.flatCount left.1 right.1
    else flatCount left.1 right.1 = 0 := by
  fin_cases left
  · exact p13MultiScaleFlatCounts_audit_00 right
  · exact p13MultiScaleFlatCounts_audit_01 right
  · exact p13MultiScaleFlatCounts_audit_02 right
  · exact p13MultiScaleFlatCounts_audit_03 right
  · exact p13MultiScaleFlatCounts_audit_04 right
  · exact p13MultiScaleFlatCounts_audit_05 right
  · exact p13MultiScaleFlatCounts_audit_06 right
  · exact p13MultiScaleFlatCounts_audit_07 right
  · exact p13MultiScaleFlatCounts_audit_08 right
  · exact p13MultiScaleFlatCounts_audit_09 right
  · exact p13MultiScaleFlatCounts_audit_10 right
  · exact p13MultiScaleFlatCounts_audit_11 right
  · exact p13MultiScaleFlatCounts_audit_12 right
  · exact p13MultiScaleFlatCounts_audit_13 right
  · exact p13MultiScaleFlatCounts_audit_14 right

end Erdos64EG.Internal
