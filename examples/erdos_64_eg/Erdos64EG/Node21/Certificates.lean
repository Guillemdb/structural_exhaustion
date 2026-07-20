import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureCertificateAudit

namespace Erdos64EG.Internal.Node21Certificates

open StructuralExhaustion
open Erdos64EG.Internal
open P13MultiScaleCurvatureCertificate

/-! Dedicated node-[21] certificate index.  The row and count producers stay
in their independently cached modules; this file is the single typed surface
consumed by the node-[21] producer. -/

structure RowCertificate (length : Fin 15) : Prop where
  exact : ∀ source : Fin 399,
    row length.1 source = semanticRow length.1 source

def row00 : RowCertificate ⟨0, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_00⟩
def row01 : RowCertificate ⟨1, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_01⟩
def row02 : RowCertificate ⟨2, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_02⟩
def row03 : RowCertificate ⟨3, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_03⟩
def row04 : RowCertificate ⟨4, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_04⟩
def row05 : RowCertificate ⟨5, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_05⟩
def row06 : RowCertificate ⟨6, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_06⟩
def row07 : RowCertificate ⟨7, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_07⟩
def row08 : RowCertificate ⟨8, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_08⟩
def row09 : RowCertificate ⟨9, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_09⟩
def row10 : RowCertificate ⟨10, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_10⟩
def row11 : RowCertificate ⟨11, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_11⟩
def row12 : RowCertificate ⟨12, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_12⟩
def row13 : RowCertificate ⟨13, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_13⟩
def row14 : RowCertificate ⟨14, by decide⟩ :=
  ⟨p13MultiScaleRows_rowAudit_14⟩

theorem allRows : ∀ length : Fin 15, RowCertificate length := by
  intro length
  fin_cases length
  · exact row00
  · exact row01
  · exact row02
  · exact row03
  · exact row04
  · exact row05
  · exact row06
  · exact row07
  · exact row08
  · exact row09
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14

structure CountCertificate : Prop where
  safeExact : ∀ left right : Fin 15,
    if 0 < left.1 ∧ 0 < right.1 ∧ left.1 + right.1 ≤ 14 then
      safeCount left.1 right.1 = profile.safeCount left.1 right.1
    else safeCount left.1 right.1 = 0
  flatExact : ∀ left right : Fin 15,
    if 0 < left.1 ∧ 0 < right.1 ∧ left.1 + right.1 ≤ 14 then
      flatCount left.1 right.1 = profile.flatCount left.1 right.1
    else flatCount left.1 right.1 = 0

def counts : CountCertificate where
  safeExact := p13MultiScaleSafeCounts_audit
  flatExact := p13MultiScaleFlatCounts_audit

end Erdos64EG.Internal.Node21Certificates
