import StructuralExhaustion.Core.ConditionalFibreRank

namespace StructuralExhaustion.Examples.ConditionalFibrePoweredBudget

open StructuralExhaustion.Core

def states : OrderedCollection (Fin 4) where
  values := [0, 1, 2, 3]
  nodup := by native_decide
  decEq := inferInstance

def coordinates : OrderedCollection (Fin 2) where
  values := [0, 1]
  nodup := by native_decide
  decEq := inferInstance

def accepts (coordinate : Fin 2) (state : Fin 4) : Bool :=
  match coordinate.1 with
  | 0 => decide (state.1 < 2)
  | _ => decide (state.1 = 0)

def profile : ConditionalFibreRank.Profile where
  State := Fin 4
  Coordinate := Fin 2
  incoming := states
  coordinates := coordinates
  accepts := accepts
  safe := 2
  flat := 1
  stateCount := 4
  stateCount_eq := by native_decide
  incomingNonempty := by native_decide

def ledger : ConditionalFibreRank.Profile.Ledger profile
    profile.incoming.values profile.coordinates.values :=
  .cons (by native_decide) (.cons (by native_decide) (.nil _ (by native_decide)))

def output :=
  ConditionalFibreProductCost.Profile.CertifiedCarrierOutput.ofLedger
    profile.stateCount_eq ledger.fibreLedger ledger.finalNonempty

/-- A non-Erdős fixture for the automatic full-fibre/powered-budget
composition. -/
theorem automatic_powered_budget :
    (2 ^ coordinates.values.length) ^ 1 <
      (1 ^ coordinates.values.length) ^ 1 * 5 := by
  exact output.forced_pow_lt_flat_pow_mul_upper
    (by change 4 < 5; norm_num) (by change 0 < 1; norm_num)

#print axioms automatic_powered_budget

end StructuralExhaustion.Examples.ConditionalFibrePoweredBudget
