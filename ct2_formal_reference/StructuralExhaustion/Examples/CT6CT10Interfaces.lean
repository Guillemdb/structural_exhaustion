import StructuralExhaustion.CT6.Interface
import StructuralExhaustion.CT7.Interface
import StructuralExhaustion.CT8.Interface
import StructuralExhaustion.CT9.Interface
import StructuralExhaustion.CT10.Interface
import StructuralExhaustion.CT11.Interface
import StructuralExhaustion.CT12.Interface
import StructuralExhaustion.CT13.Interface
import StructuralExhaustion.CT14.Interface
import StructuralExhaustion.CT15.Interface
import StructuralExhaustion.CT16.Interface
import StructuralExhaustion.CT17.Interface

namespace StructuralExhaustion.Examples.CT6CT10Fixtures

open StructuralExhaustion

def ct6Entry : CT6.Interface.Framework where
  Ambient := Unit
  BranchState := fun _ => Unit
  Monitor := fun _ _ => Unit
  Threshold := fun _ _ => Unit
  FailureOrder := fun _ _ => Unit
  FailureWitness := fun _ _ => Unit
  ScopeReady := fun _ _ _ _ => True
  C1Claim := fun _ _ => True

def ct6Input : CT6.Interface.Input ct6Entry where
  G := (); branch := (); monitor := (); threshold := (); failureOrder := ()

def ct7Entry : CT7.Interface.Framework where
  Ambient := Unit
  BranchState := fun _ => Unit
  Object := fun _ _ => Unit
  Boundary := fun _ _ => Unit
  ExchangeWitness := fun _ _ => Unit
  ContextSystem := fun _ _ => Unit
  ScopeReady := fun _ _ _ _ _ _ => True
  C1Claim := fun _ _ => True
  C2Claim := fun _ _ => True
  C3Claim := fun _ _ => True

def ct7Input : CT7.Interface.Input ct7Entry where
  G := (); branch := (); left := (); right := (); boundary := ()
  exchange := (); contexts := ()

def ct8Entry : CT8.Interface.Framework where
  Ambient := Unit
  BranchState := fun _ => Unit
  Sequence := fun _ _ => Unit
  TypeSystem := fun _ _ => Unit
  Threshold := fun _ _ => Unit
  ScopeReady := fun _ _ _ _ => True
  C2Claim := fun _ _ => True
  C5Claim := fun _ _ => True

def ct8Input : CT8.Interface.Input ct8Entry where
  G := (); branch := (); sequence := (); typeSystem := (); threshold := ()

def ct9Entry : CT9.Interface.Framework where
  Ambient := Unit
  BranchState := fun _ => Unit
  Payer := fun _ _ => Unit
  Fibre := fun _ _ => Unit
  Labels := fun _ _ => Unit
  Capacity := fun _ _ => Unit
  ScopeReady := fun _ _ _ _ _ => True
  C1Claim := fun _ _ => True

def ct9Input : CT9.Interface.Input ct9Entry where
  G := (); branch := (); payer := (); fibre := (); labels := (); capacity := ()

def ct10Entry : CT10.Interface.Framework where
  Ambient := Unit
  BranchState := fun _ => Unit
  ResidualClass := fun _ _ => Unit
  MissingDatum := fun _ _ => Unit
  Alphabet := fun _ _ => Unit
  ClassTable := fun _ _ => Unit
  ScopeReady := fun _ _ _ _ _ => True
  C5Claim := fun _ _ => True

def ct10Input : CT10.Interface.Input ct10Entry where
  G := (); branch := (); residual := (); datum := (); alphabet := (); table := ()

def ct11Entry : CT11.Interface.Framework where
  Ambient := Unit; BranchState := fun _ => Unit; Deficit := fun _ _ => Unit
  Decomposition := fun _ _ => Unit; Admissibility := fun _ _ => Unit
  LocalType := fun _ _ => Unit; ScopeReady := fun _ _ _ _ _ => True
def ct11Input : CT11.Interface.Input ct11Entry where
  G := (); branch := (); deficit := (); decomposition := (); admissibility := (); localType := ()

def ct12Entry : CT12.Interface.Framework where
  Ambient := Unit; BranchState := fun _ => Unit; LoadAccount := fun _ _ => Unit
  PeelMove := fun _ _ => Unit; ScopeReady := fun _ _ _ _ => True
  C4Claim := fun _ _ => True
def ct12Input : CT12.Interface.Input ct12Entry where
  G := (); branch := (); account := (); peelMove := (); load := 1

def ct13Entry : CT13.Interface.Framework where
  Ambient := Unit; BranchState := fun _ => Unit; TierAccount := fun _ _ => Unit
  Availability := fun _ _ => Unit; Resource := fun _ _ => Unit
  ScopeReady := fun _ _ _ _ => True; C4Claim := fun _ _ => True
def ct13Input : CT13.Interface.Input ct13Entry where
  G := (); branch := (); account := (); availability := (); resource := ()

def ct14Entry : CT14.Interface.Framework where
  Ambient := Unit; BranchState := fun _ => Unit; ResidualClass := fun _ _ => Unit
  LowerMass := fun _ _ => Unit; Capacity := fun _ _ => Unit; Multiplicity := fun _ _ => Unit
  ScopeReady := fun _ _ _ _ _ => True; C4Claim := fun _ _ => True
def ct14Input : CT14.Interface.Input ct14Entry where
  G := (); branch := (); residual := (); lowerMass := (); capacity := (); multiplicity := ()

def ct15Entry : CT15.Interface.Framework where
  Ambient := Unit; BranchState := fun _ => Unit; TestFamily := fun _ _ => Unit
  RankMap := fun _ _ => Unit; TargetData := fun _ _ => Unit; Capacity := fun _ _ => Unit
  ScopeReady := fun _ _ _ _ _ => True; C4Claim := fun _ _ => True
def ct15Input : CT15.Interface.Input ct15Entry where
  G := (); branch := (); tests := (); rankMap := (); target := (); capacity := ()

def ct16Entry : CT16.Interface.Framework where
  Ambient := Unit; BranchState := fun _ => Unit; Support := fun _ _ => Unit
  WholeDatum := fun _ _ => Unit; ClosedTypeData := fun _ _ => Unit
  ScopeReady := fun _ _ _ _ => True; C2Claim := fun _ _ => True
def ct16Input : CT16.Interface.Input ct16Entry where
  G := (); branch := (); support := (); datum := (); closedType := ()

def ct17Entry : CT17.Interface.Framework where
  Ambient := Unit; BranchState := fun _ => Unit; TargetSet := fun _ _ => Unit
  OffsetFamily := fun _ _ => Unit; CompletionClasses := fun _ _ => Unit
  ArithmeticData := fun _ _ => Unit; ScopeReady := fun _ _ _ _ _ => True
  C1Claim := fun _ _ => True; C5Claim := fun _ _ => True
def ct17Input : CT17.Interface.Input ct17Entry where
  G := (); branch := (); targetSet := (); offsets := (); completions := (); arithmetic := ()

end StructuralExhaustion.Examples.CT6CT10Fixtures
