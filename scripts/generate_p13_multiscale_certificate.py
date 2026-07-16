#!/usr/bin/env python3
"""Generate the fixed node-[21] P13 multi-scale Lean certificate.

The generator deliberately uses only integer bit operations.  Lean rechecks
the emitted relation rows against `P13CodeCompatibleSparse` and rechecks the
emitted counts through `Core.FiniteBitRelationBarrier` in independent shards.
"""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "examples/erdos_64_eg/Erdos64EG"
WIDTH = 13
LABEL_COUNT = 399
MATRIX_WIDTH = 399


FORBIDDEN_GAPS = {
    0: (2, 6),
    1: (1, 5),
    2: (0, 4, 12),
    3: (3, 11),
    4: (2, 10),
    5: (1, 9),
    6: (0, 8),
    7: (7,),
    8: (6,),
    9: (5,),
    10: (4,),
    11: (3,),
    12: (2,),
    13: (1,),
    14: (0,),
}


def legal(code: int) -> bool:
    return code != 0 and not (code & (code >> 2)) and not (code & (code >> 6))


def compatible(shift: int, left: int, right: int) -> bool:
    for gap in FORBIDDEN_GAPS[shift]:
        if gap == 0:
            if left & right:
                return False
        elif left & (right >> gap) or right & (left >> gap):
            return False
    return True


def relation_rows(codes: list[int]) -> list[list[int]]:
    return [
        [
            sum(1 << j for j, right in enumerate(codes)
                if compatible(shift, left, right))
            for left in codes
        ]
        for shift in range(15)
    ]


def safe_count(rows: list[list[int]], left: int, right: int) -> int:
    return sum(row_left.bit_count() * row_right.bit_count()
               for row_left, row_right in zip(rows[left], rows[right]))


def flat_count(rows: list[list[int]], left: int, right: int) -> int:
    total = 0
    for source, left_row in enumerate(rows[left]):
        composed_row = rows[left + right][source]
        bits = left_row
        while bits:
            bit = bits & -bits
            middle = bit.bit_length() - 1
            total += (rows[right][middle] & composed_row).bit_count()
            bits ^= bit
    return total


def lean_nat_array(values: list[int], indent: str = "  ") -> str:
    return "#[\n" + ",\n".join(f"{indent}{value}" for value in values) + "\n]"


def write_certificate(rows: list[list[int]], safe: list[int], flat: list[int]) -> None:
    row_arrays = []
    for shift_rows in rows:
        entries = ",\n".join(
            f"      BitVec.ofNat {MATRIX_WIDTH} {value}" for value in shift_rows
        )
        row_arrays.append("    #[\n" + entries + "\n    ]")
    text = f"""import Erdos64EG.P13MultiScaleBitSemantic
import StructuralExhaustion.Core.FiniteBitRelationBarrier

namespace Erdos64EG.Internal.P13MultiScaleCurvatureCertificate

open StructuralExhaustion

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Generated fixed certificate for all fifteen P13 compatibility relations.
Rows follow the verified CT10 legal-code order.  Separate audit modules
recheck every bit against `P13CodeCompatibleSparse` and every accepted count
against `Core.FiniteBitRelationBarrier` before downstream use.
-/

def rows : Array (Array (BitVec {MATRIX_WIDTH})) := #[
{',\n'.join(row_arrays)}
]

/-- Slot `15 * leftLength + rightLength`; zero outside the 91 accepted pairs. -/
def safeCounts : Array Nat := {lean_nat_array(safe)}

/-- Slot `15 * leftLength + rightLength`; zero outside the 91 accepted pairs. -/
def flatCounts : Array Nat := {lean_nat_array(flat)}

def row (length : Nat) (source : Fin {LABEL_COUNT}) : BitVec {MATRIX_WIDTH} :=
  (rows.getD length #[]).getD source.1 0#{MATRIX_WIDTH}

def profile : Core.FiniteBitRelationBarrier.Profile {LABEL_COUNT} where
  row := row

def safeCount (leftLength rightLength : Nat) : Nat :=
  safeCounts.getD (15 * leftLength + rightLength) 0

def flatCount (leftLength rightLength : Nat) : Nat :=
  flatCounts.getD (15 * leftLength + rightLength) 0

theorem shape : rows.size = 15 ∧
    (∀ length : Fin 15, (rows.getD length.1 #[]).size = {LABEL_COUNT}) ∧
    safeCounts.size = 225 ∧ flatCounts.size = 225 := by
  native_decide

end Erdos64EG.Internal.P13MultiScaleCurvatureCertificate
"""
    (OUT / "P13MultiScaleCurvatureCertificate.lean").write_text(text)


def write_audit_shard(shift: int) -> None:
    text = f"""import Erdos64EG.P13MultiScaleCurvatureCertificate

namespace Erdos64EG.Internal

open StructuralExhaustion
open P13MultiScaleCurvatureCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Independent audit shard for connector length `{shift}`. -/

theorem p13MultiScaleRows_codeAudit_{shift:02d} : ∀ source target : Fin 399,
    (row {shift} source).getLsb target =
      @decide (P13CodeCompatibleSparse {shift}
        (p13CurvatureCodes.getD source.1 0#13)
        (p13CurvatureCodes.getD target.1 0#13))
        (p13CodeCompatibleSparseDecidable {shift} _ _) := by
  native_decide

theorem p13MultiScaleSafeCounts_audit_{shift:02d} : ∀ right : Fin 15,
    if 0 < {shift} ∧ 0 < right.1 ∧ {shift} + right.1 ≤ 14 then
      safeCount {shift} right.1 = profile.safeCount {shift} right.1
    else safeCount {shift} right.1 = 0 := by
  native_decide

theorem p13MultiScaleFlatCounts_audit_{shift:02d} : ∀ right : Fin 15,
    if 0 < {shift} ∧ 0 < right.1 ∧ {shift} + right.1 ≤ 14 then
      flatCount {shift} right.1 = profile.flatCount {shift} right.1
    else flatCount {shift} right.1 = 0 := by
  native_decide

end Erdos64EG.Internal
"""
    (OUT / f"P13MultiScaleCurvatureAudit{shift:02d}.lean").write_text(text)


def write_aggregate_audit() -> None:
    imports = "\n".join(
        f"import Erdos64EG.P13MultiScaleCurvatureAudit{shift:02d}"
        for shift in range(15)
    )
    row_cases = "\n".join(
        f"  · exact p13MultiScaleRows_codeAudit_{shift:02d} source target"
        for shift in range(15)
    )
    safe_cases = "\n".join(
        f"  · exact p13MultiScaleSafeCounts_audit_{shift:02d} right"
        for shift in range(15)
    )
    flat_cases = "\n".join(
        f"  · exact p13MultiScaleFlatCounts_audit_{shift:02d} right"
        for shift in range(15)
    )
    text = f"""{imports}

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
{row_cases}

theorem p13MultiScaleSafeCounts_audit (left right : Fin 15) :
    if 0 < left.1 ∧ 0 < right.1 ∧ left.1 + right.1 ≤ 14 then
      safeCount left.1 right.1 = profile.safeCount left.1 right.1
    else safeCount left.1 right.1 = 0 := by
  fin_cases left
{safe_cases}

theorem p13MultiScaleFlatCounts_audit (left right : Fin 15) :
    if 0 < left.1 ∧ 0 < right.1 ∧ left.1 + right.1 ≤ 14 then
      flatCount left.1 right.1 = profile.flatCount left.1 right.1
    else flatCount left.1 right.1 = 0 := by
  fin_cases left
{flat_cases}

end Erdos64EG.Internal
"""
    (OUT / "P13MultiScaleCurvatureCertificateAudit.lean").write_text(text)


def main() -> None:
    codes = [code for code in range(1 << WIDTH) if legal(code)]
    assert len(codes) == LABEL_COUNT
    rows = relation_rows(codes)
    safe = [0] * 225
    flat = [0] * 225
    for left in range(1, 14):
        for right in range(1, 15 - left):
            slot = 15 * left + right
            safe[slot] = safe_count(rows, left, right)
            flat[slot] = flat_count(rows, left, right)
    assert safe[16] == 543958
    assert flat[16] == 111286
    write_certificate(rows, safe, flat)
    for shift in range(15):
        write_audit_shard(shift)
    write_aggregate_audit()


if __name__ == "__main__":
    main()
