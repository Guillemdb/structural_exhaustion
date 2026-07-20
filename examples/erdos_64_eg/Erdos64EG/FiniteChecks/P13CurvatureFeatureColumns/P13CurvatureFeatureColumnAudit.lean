import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit00
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit01
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit02
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit03
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit04
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit05
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit06
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit07
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit08
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit09
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit10
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit11
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit12

namespace Erdos64EG.Internal

/-- The thirteen stored feature columns exactly encode the bits of every
ascending-carrier code. -/
theorem p13AscendingFeatureColumn_exact
    (feature : Fin 13) (target : Fin 399) :
    (p13AscendingFeatureColumn feature).getLsb target =
      (p13AscendingCode target).getLsb feature := by
  fin_cases feature
  · exact p13AscendingFeatureColumn_audit_00 target
  · exact p13AscendingFeatureColumn_audit_01 target
  · exact p13AscendingFeatureColumn_audit_02 target
  · exact p13AscendingFeatureColumn_audit_03 target
  · exact p13AscendingFeatureColumn_audit_04 target
  · exact p13AscendingFeatureColumn_audit_05 target
  · exact p13AscendingFeatureColumn_audit_06 target
  · exact p13AscendingFeatureColumn_audit_07 target
  · exact p13AscendingFeatureColumn_audit_08 target
  · exact p13AscendingFeatureColumn_audit_09 target
  · exact p13AscendingFeatureColumn_audit_10 target
  · exact p13AscendingFeatureColumn_audit_11 target
  · exact p13AscendingFeatureColumn_audit_12 target

end Erdos64EG.Internal
