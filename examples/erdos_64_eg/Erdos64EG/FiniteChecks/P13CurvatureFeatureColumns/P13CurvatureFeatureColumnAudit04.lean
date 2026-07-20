import Erdos64EG.FiniteChecks.P13Curvature.P13CurvatureAscendingCarrier
import StructuralExhaustion.Core.FiniteBitRelationBarrier

namespace Erdos64EG.Internal

/-! Chunked pointwise audit for ascending-carrier feature 4. -/

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_00 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            0 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            0 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_01 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            16 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            16 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_02 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            32 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            32 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_03 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            48 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            48 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_04 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            64 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            64 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_05 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            80 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            80 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_06 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            96 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            96 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_07 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            112 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            112 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_08 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            128 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            128 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_09 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            144 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            144 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_10 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            160 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            160 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_11 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            176 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            176 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_12 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            192 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            192 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_13 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            208 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            208 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_14 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            224 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            224 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_15 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            240 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            240 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_16 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            256 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            256 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_17 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            272 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            272 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_18 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            288 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            288 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_19 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            304 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            304 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_20 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            320 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            320 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_21 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            336 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            336 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_22 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            352 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            352 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_23 :
    ∀ offset : Fin 16,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            368 16 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            368 16 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

set_option exponentiation.threshold 512 in
private theorem p13AscendingFeatureColumn_audit_04_24 :
    ∀ offset : Fin 15,
      (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            384 15 (by decide) offset) =
        (p13AscendingCode
          (StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalIndex
            384 15 (by decide) offset)).getLsb ⟨4, by decide⟩ := by
  decide

theorem p13AscendingFeatureColumn_audit_04 (target : Fin 399) :
    (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb target =
      (p13AscendingCode target).getLsb ⟨4, by decide⟩ := by
  let retrieve :=
    StructuralExhaustion.Core.FiniteBitRelationBarrier.intervalEquality_at
      (fun target : Fin 399 =>
        (p13AscendingFeatureColumn ⟨4, by decide⟩).getLsb target)
      (fun target : Fin 399 =>
        (p13AscendingCode target).getLsb ⟨4, by decide⟩)
  by_cases before16 : target.1 < 16
  · exact retrieve
      (start := 0) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_00
      target (by omega) before16
  by_cases before32 : target.1 < 32
  · exact retrieve
      (start := 16) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_01
      target (by omega) before32
  by_cases before48 : target.1 < 48
  · exact retrieve
      (start := 32) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_02
      target (by omega) before48
  by_cases before64 : target.1 < 64
  · exact retrieve
      (start := 48) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_03
      target (by omega) before64
  by_cases before80 : target.1 < 80
  · exact retrieve
      (start := 64) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_04
      target (by omega) before80
  by_cases before96 : target.1 < 96
  · exact retrieve
      (start := 80) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_05
      target (by omega) before96
  by_cases before112 : target.1 < 112
  · exact retrieve
      (start := 96) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_06
      target (by omega) before112
  by_cases before128 : target.1 < 128
  · exact retrieve
      (start := 112) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_07
      target (by omega) before128
  by_cases before144 : target.1 < 144
  · exact retrieve
      (start := 128) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_08
      target (by omega) before144
  by_cases before160 : target.1 < 160
  · exact retrieve
      (start := 144) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_09
      target (by omega) before160
  by_cases before176 : target.1 < 176
  · exact retrieve
      (start := 160) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_10
      target (by omega) before176
  by_cases before192 : target.1 < 192
  · exact retrieve
      (start := 176) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_11
      target (by omega) before192
  by_cases before208 : target.1 < 208
  · exact retrieve
      (start := 192) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_12
      target (by omega) before208
  by_cases before224 : target.1 < 224
  · exact retrieve
      (start := 208) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_13
      target (by omega) before224
  by_cases before240 : target.1 < 240
  · exact retrieve
      (start := 224) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_14
      target (by omega) before240
  by_cases before256 : target.1 < 256
  · exact retrieve
      (start := 240) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_15
      target (by omega) before256
  by_cases before272 : target.1 < 272
  · exact retrieve
      (start := 256) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_16
      target (by omega) before272
  by_cases before288 : target.1 < 288
  · exact retrieve
      (start := 272) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_17
      target (by omega) before288
  by_cases before304 : target.1 < 304
  · exact retrieve
      (start := 288) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_18
      target (by omega) before304
  by_cases before320 : target.1 < 320
  · exact retrieve
      (start := 304) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_19
      target (by omega) before320
  by_cases before336 : target.1 < 336
  · exact retrieve
      (start := 320) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_20
      target (by omega) before336
  by_cases before352 : target.1 < 352
  · exact retrieve
      (start := 336) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_21
      target (by omega) before352
  by_cases before368 : target.1 < 368
  · exact retrieve
      (start := 352) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_22
      target (by omega) before368
  by_cases before384 : target.1 < 384
  · exact retrieve
      (start := 368) (width := 16)
      (by decide) p13AscendingFeatureColumn_audit_04_23
      target (by omega) before384
  exact retrieve
    (start := 384) (width := 15)
    (by decide) p13AscendingFeatureColumn_audit_04_24
    target (by omega) target.isLt

end Erdos64EG.Internal

