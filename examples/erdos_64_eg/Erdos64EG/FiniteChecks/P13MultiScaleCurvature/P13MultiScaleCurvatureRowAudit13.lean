import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 10000

/-! Packed-row audit for connector length `13`. -/

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_00 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            0 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            0 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_01 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            16 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            16 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_02 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            32 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            32 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_03 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            48 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            48 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_04 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            64 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            64 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_05 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            80 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            80 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_06 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            96 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            96 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_07 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            112 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            112 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_08 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            128 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            128 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_09 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            144 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            144 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_10 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            160 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            160 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_11 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            176 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            176 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_12 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            192 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            192 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_13 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            208 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            208 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_14 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            224 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            224 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_15 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            240 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            240 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_16 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            256 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            256 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_17 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            272 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            272 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_18 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            288 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            288 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_19 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            304 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            304 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_20 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            320 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            320 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_21 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            336 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            336 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_22 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            352 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            352 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_23 :
    ∀ offset : Fin 16,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            368 16 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            368 16 (by decide) offset) := by
  native_decide

set_option exponentiation.threshold 512 in
private theorem p13MultiScaleRows_featureAudit_13_24 :
    ∀ offset : Fin 15,
      row 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            384 15 (by decide) offset) =
        p13FeatureCompatibilityRow 13
          (Core.FiniteBitRelationBarrier.intervalIndex
            384 15 (by decide) offset) := by
  native_decide

private theorem p13MultiScaleRows_featureAudit_13 :
    ∀ source : Fin 399,
      row 13 source = p13FeatureCompatibilityRow 13 source := by
  intro source
  let retrieve :=
    Core.FiniteBitRelationBarrier.intervalEquality_at
      (fun source : Fin 399 => row 13 source)
      (fun source : Fin 399 => p13FeatureCompatibilityRow 13 source)
  by_cases before16 : source.1 < 16
  · exact retrieve
      (start := 0) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_00
      source (by omega) before16
  by_cases before32 : source.1 < 32
  · exact retrieve
      (start := 16) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_01
      source (by omega) before32
  by_cases before48 : source.1 < 48
  · exact retrieve
      (start := 32) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_02
      source (by omega) before48
  by_cases before64 : source.1 < 64
  · exact retrieve
      (start := 48) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_03
      source (by omega) before64
  by_cases before80 : source.1 < 80
  · exact retrieve
      (start := 64) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_04
      source (by omega) before80
  by_cases before96 : source.1 < 96
  · exact retrieve
      (start := 80) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_05
      source (by omega) before96
  by_cases before112 : source.1 < 112
  · exact retrieve
      (start := 96) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_06
      source (by omega) before112
  by_cases before128 : source.1 < 128
  · exact retrieve
      (start := 112) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_07
      source (by omega) before128
  by_cases before144 : source.1 < 144
  · exact retrieve
      (start := 128) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_08
      source (by omega) before144
  by_cases before160 : source.1 < 160
  · exact retrieve
      (start := 144) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_09
      source (by omega) before160
  by_cases before176 : source.1 < 176
  · exact retrieve
      (start := 160) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_10
      source (by omega) before176
  by_cases before192 : source.1 < 192
  · exact retrieve
      (start := 176) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_11
      source (by omega) before192
  by_cases before208 : source.1 < 208
  · exact retrieve
      (start := 192) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_12
      source (by omega) before208
  by_cases before224 : source.1 < 224
  · exact retrieve
      (start := 208) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_13
      source (by omega) before224
  by_cases before240 : source.1 < 240
  · exact retrieve
      (start := 224) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_14
      source (by omega) before240
  by_cases before256 : source.1 < 256
  · exact retrieve
      (start := 240) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_15
      source (by omega) before256
  by_cases before272 : source.1 < 272
  · exact retrieve
      (start := 256) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_16
      source (by omega) before272
  by_cases before288 : source.1 < 288
  · exact retrieve
      (start := 272) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_17
      source (by omega) before288
  by_cases before304 : source.1 < 304
  · exact retrieve
      (start := 288) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_18
      source (by omega) before304
  by_cases before320 : source.1 < 320
  · exact retrieve
      (start := 304) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_19
      source (by omega) before320
  by_cases before336 : source.1 < 336
  · exact retrieve
      (start := 320) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_20
      source (by omega) before336
  by_cases before352 : source.1 < 352
  · exact retrieve
      (start := 336) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_21
      source (by omega) before352
  by_cases before368 : source.1 < 368
  · exact retrieve
      (start := 352) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_22
      source (by omega) before368
  by_cases before384 : source.1 < 384
  · exact retrieve
      (start := 368) (width := 16)
      (by decide) p13MultiScaleRows_featureAudit_13_23
      source (by omega) before384
  exact retrieve
    (start := 384) (width := 15)
    (by decide) p13MultiScaleRows_featureAudit_13_24
    source (by omega) source.isLt

theorem p13MultiScaleRows_rowAudit_13 : ∀ source : Fin 399,
    row 13 source = semanticRow 13 source := by
  intro source
  calc
    row 13 source = p13FeatureCompatibilityRow 13 source :=
      p13MultiScaleRows_featureAudit_13 source
    _ = semanticRow 13 source :=
      p13FeatureCompatibilityRow_eq_semanticRow 13 source

theorem p13MultiScaleRows_codeAudit_13 : ∀ source target : Fin 399,
    (row 13 source).getLsb target = semanticRelation 13 source target := by
  intro source target
  rw [p13MultiScaleRows_rowAudit_13 source]
  exact Core.FiniteBitRelationBarrier.semanticRow_getLsb _ _ _

end Erdos64EG.Internal
