import Hypostructure.Core.FiniteBitRelationBarrier
import HypostructureErdos64EG.Node20

namespace HypostructureErdos64EG

open Hypostructure

universe u w x

/-! Node21 is the generic finite barrier-table continuation on the low branch.
The application supplies only the table certificate and its index semantics. -/

structure Node21Contract (Previous : Type u) (Table : Type w) (Index : Type x) where
  certificate : Table
  index : Index

structure Node21Output (Previous : Type u) (Table : Type w) (Index : Type x) where
  contract : Node21Contract Previous Table Index

/-! Certified alternative for the production path.  The finite relation
barrier is owned by Core; this node only registers the certificate as a new
ledger fact. -/
structure Node21CertifiedContract (Previous : Type u) (size : Nat)
    (Length : Type w) (Index : Type x) where
  lengthValue : Length -> Nat
  relation : Length -> Fin size -> Fin size -> Bool
  profile : Core.FiniteBitRelationBarrier.Profile size
  table : Core.FiniteBitRelationBarrier.CertifiedTable profile Length
    lengthValue relation Index

structure Node21CertifiedOutput
    (contract : Node21CertifiedContract Previous size Length Index) where
  certificate : Core.FiniteBitRelationBarrier.CertifiedTable
    contract.profile Length contract.lengthValue contract.relation Index

abbrev Node21CertifiedStage (contract : Node21CertifiedContract Previous size Length Index) :=
  Core.Residual.Ledger.Extension Previous (fun _ => Node21CertifiedOutput contract)

noncomputable def node21Certified
    (contract : Node21CertifiedContract Previous size Length Index)
    (previous : Previous) : Node21CertifiedStage contract :=
  Core.Residual.Ledger.extend previous { certificate := contract.table }

abbrev Node21Stage (contract : Node19Contract Previous)
    (Table' : Type w) (Index : Type x) :=
  Core.Residual.Ledger.Extension (Node19Stage contract)
    (fun _stage => Node21Output Previous Table' Index)

noncomputable def node21 (contract : Node19Contract Previous)
    (certificate : Table') (index : Index)
    (previous : Node19Stage contract) : Node21Stage contract Table' Index :=
  Core.Residual.Ledger.extend previous
    { contract := { certificate := certificate, index := index } }

end HypostructureErdos64EG
