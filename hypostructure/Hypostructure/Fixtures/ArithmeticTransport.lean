import Hypostructure.Core.ArithmeticTransport

/-!
# Domain-neutral arithmetic transport fixture

The values here are only a small kernel-checking witness for the reusable
arithmetic contracts.  No graph or PDE semantics are imported.
-/

namespace Hypostructure.Fixtures.ArithmeticTransport

open Hypostructure.Core.ArithmeticTransport

def powered : PoweredTransfer.Profile where
  forced := 2
  flat := 2
  stateCount := 1
  upper := 2
  scale := 1
  forced_le_flat_mul_stateCount := by decide
  stateCount_pow_lt_upper := by decide
  flat_pos := by decide

theorem powered_transfer :
    powered.forced ^ powered.scale < powered.flat ^ powered.scale * powered.upper :=
  PoweredTransfer.forced_pow_lt_flat_pow_mul_upper powered

def capacity : PoweredCapacity where
  stateCount := 1
  base := 2
  exponent := 1
  paidExponent := 0
  desiredExponent := 1
  errorExponent := 1
  capacity := 2
  paid := by decide
  desired_eq := by decide

theorem capacity_error :
    capacity.stateCount ^ capacity.exponent * capacity.base ^ capacity.desiredExponent ≤
      capacity.capacity ^ capacity.exponent * capacity.base ^ capacity.errorExponent :=
  capacity.with_error

theorem quarter_charge :
    4 * (1 : Int) - (5 : Int) < 0 := by
  exact StrictGap.quarter_charge_negative (by decide)

end Hypostructure.Fixtures.ArithmeticTransport
