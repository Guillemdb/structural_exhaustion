import StructuralExhaustion.Core.ConditionalFibreProductCost

namespace StructuralExhaustion.Core.ConditionalFibreRank

universe u v

open ConditionalFibreProductCost

/-- A rank profile is fixed to one literal incoming residual carrier. -/
structure Profile where
  State : Type u
  Coordinate : Type v
  incoming : OrderedCollection State
  coordinates : OrderedCollection Coordinate
  accepts : Coordinate → State → Bool
  safe : Nat
  flat : Nat
  stateCount : Nat
  stateCount_eq : stateCount = incoming.values.length
  incomingNonempty : 0 < incoming.values.length

namespace Profile

def costProfile (profile : Profile.{u, v}) :
    ConditionalFibreProductCost.Profile :=
  ConditionalFibreProductCost.Profile.onCarrier
    profile.incoming profile.coordinates profile.accepts
    profile.safe profile.flat profile.stateCount

def retain (profile : Profile.{u, v}) (states : List profile.State)
    (coordinate : profile.Coordinate) : List profile.State :=
  states.filter (profile.accepts coordinate)

/-- A rank coordinate succeeds only when its exact conditional inequality
pays and the retained realization fibre remains nonempty. -/
def Pays (profile : Profile.{u, v}) (states : List profile.State)
    (coordinate : profile.Coordinate) : Prop :=
  profile.safe * (profile.retain states coordinate).length ≤
      profile.flat * states.length ∧
    0 < (profile.retain states coordinate).length

instance (profile : Profile.{u, v}) (states : List profile.State)
    (coordinate : profile.Coordinate) : Decidable (profile.Pays states coordinate) :=
  by unfold Pays; infer_instance

inductive Ledger (profile : Profile.{u, v}) :
    List profile.State → List profile.Coordinate → Type (max u v)
  | nil (states : List profile.State) (nonempty : 0 < states.length) :
      Ledger profile states []
  | cons {states : List profile.State} {coordinate : profile.Coordinate}
      {coordinates : List profile.Coordinate}
      (pays : profile.Pays states coordinate)
      (tail : Ledger profile (profile.retain states coordinate) coordinates) :
      Ledger profile states (coordinate :: coordinates)

namespace Ledger

def fibreLedger {profile : Profile.{u, v}} {states : List profile.State} :
    {coordinates : List profile.Coordinate} →
      profile.Ledger states coordinates →
      ConditionalFibreProductCost.Profile.Ledger profile.costProfile states coordinates
  | [], .nil _ _ => .nil _
  | _ :: _, .cons pays tail => .cons pays.1 tail.fibreLedger

theorem finalNonempty {profile : Profile.{u, v}} {states : List profile.State}
    {coordinates : List profile.Coordinate}
    (ledger : profile.Ledger states coordinates) :
    0 < ledger.fibreLedger.finalStates.length := by
  induction ledger with
  | nil states nonempty => exact nonempty
  | cons pays tail ih => exact ih

end Ledger

/-- A certified subfamily is an initial subfamily of the authored coordinate
schedule.  It never changes or re-enumerates the incoming state carrier. -/
def CertifiedPrefix (profile : Profile.{u, v}) (size : Nat) : Prop :=
  ∃ ledger : profile.Ledger profile.incoming.values
      (profile.coordinates.values.take size), True

/-- Target rank is literally the largest certified coordinate subfamily. -/
noncomputable def targetRank (profile : Profile.{u, v}) : Nat := by
  classical
  exact Nat.findGreatest profile.CertifiedPrefix profile.coordinates.values.length

theorem targetRank_le (profile : Profile.{u, v}) :
    profile.targetRank ≤ profile.coordinates.values.length := by
  classical
  exact Nat.findGreatest_le _

inductive FirstFailure (profile : Profile.{u, v}) :
    List profile.State → List profile.Coordinate → Type (max u v)
  | here {states coordinate coordinates}
      (fails : ¬profile.Pays states coordinate) :
      FirstFailure profile states (coordinate :: coordinates)
  | later {states coordinate coordinates}
      (pays : profile.Pays states coordinate)
      (failure : FirstFailure profile (profile.retain states coordinate) coordinates) :
      FirstFailure profile states (coordinate :: coordinates)

namespace FirstFailure

def coordinate {profile : Profile.{u, v}} {states coordinates}
    (failure : profile.FirstFailure states coordinates) : profile.Coordinate :=
  match failure with
  | .here (coordinate := coordinate) _ => coordinate
  | .later _ tail => tail.coordinate

theorem incompatible {profile : Profile.{u, v}} {states coordinates}
    (failure : profile.FirstFailure states coordinates)
    (ledger : profile.Ledger states coordinates) : False := by
  induction failure with
  | here fails => cases ledger with | cons pays _ => exact fails pays
  | later _ failure ih => cases ledger with | cons _ tail => exact ih tail

end FirstFailure

inductive Outcome (profile : Profile.{u, v}) where
  | dropped
      (rank_lt : profile.targetRank < profile.coordinates.values.length)
      (failure : profile.FirstFailure profile.incoming.values
        profile.coordinates.values)
  | full
      (output : ConditionalFibreProductCost.Profile.CertifiedCarrierOutput
        profile.incoming profile.coordinates
        profile.accepts profile.safe profile.flat profile.stateCount)

private def runFrom (profile : Profile.{u, v}) :
    (states : List profile.State) → 0 < states.length →
      (coordinates : List profile.Coordinate) →
      Sum (profile.FirstFailure states coordinates) (profile.Ledger states coordinates)
  | states, nonempty, [] => .inr (.nil states nonempty)
  | states, _nonempty, coordinate :: coordinates =>
      if pays : profile.Pays states coordinate then
        match profile.runFrom (profile.retain states coordinate) pays.2 coordinates with
        | .inl failure => .inl (.later pays failure)
        | .inr ledger => .inr (.cons pays ledger)
      else .inl (.here pays)

/-- Framework-owned rank split.  The full terminal contains the complete
carrier-indexed cost certificate; the other terminal exposes the canonical
first failed coordinate and a strict target-rank drop. -/
noncomputable def run (profile : Profile.{u, v}) : profile.Outcome := by
  classical
  cases result : profile.runFrom profile.incoming.values
      profile.incomingNonempty profile.coordinates.values with
  | inr ledger =>
      exact .full
        (ConditionalFibreProductCost.Profile.CertifiedCarrierOutput.ofLedger
          profile.stateCount_eq
        ledger.fibreLedger ledger.finalNonempty)
  | inl failure =>
      have rank_lt : profile.targetRank < profile.coordinates.values.length := by
        have notFull : ¬profile.CertifiedPrefix
            profile.coordinates.values.length := by
          intro certified
          obtain ⟨ledger, _⟩ := certified
          have ledgerFull : profile.Ledger profile.incoming.values
              profile.coordinates.values := by
            simpa using ledger
          exact failure.incompatible ledgerFull
        have upper := profile.targetRank_le
        have unequal : profile.targetRank ≠ profile.coordinates.values.length := by
          intro equal
          have existsFull : profile.CertifiedPrefix
              profile.coordinates.values.length := by
            unfold targetRank at equal
            have base : profile.CertifiedPrefix 0 := by
              refine ⟨?_, trivial⟩
              simpa using Profile.Ledger.nil profile.incoming.values
                profile.incomingNonempty
            have found := Nat.findGreatest_spec
              (P := profile.CertifiedPrefix)
              (m := 0)
              (n := profile.coordinates.values.length)
              (by omega) base
            rw [equal] at found
            exact found
          exact notFull existsFull
        omega
      exact Outcome.dropped rank_lt failure

end Profile

end StructuralExhaustion.Core.ConditionalFibreRank
