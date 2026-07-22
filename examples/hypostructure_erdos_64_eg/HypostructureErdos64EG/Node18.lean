import Hypostructure.Core.FiniteBitRelationBarrier
import HypostructureErdos64EG.Node17

namespace HypostructureErdos64EG

open Hypostructure

universe u v w x y

/-! Node18 is the application entry for a finite CT10 relation table.  The
table is supplied by the theorem contract; Core owns its semantic and count
certificate shape and no graph-specific label representation is introduced. -/

/-! A node-[18] table is not an opaque application payload.  It must carry
the semantic row certificate and the exact stored count columns owned by
Core's finite bit-relation barrier API. -/
structure Node18Contract (size : Nat) (Length : Type x) (Index : Type y) where
  lengthValue : Length -> Nat
  relation : Length -> Fin size -> Fin size -> Bool
  profile : Core.FiniteBitRelationBarrier.Profile size
  table : Core.FiniteBitRelationBarrier.CertifiedTable profile Length
    lengthValue relation Index

structure Node18Output (Table : Type w) where
  table : Table

structure Node18CertifiedOutput (size : Nat) (Length : Type x) (Index : Type y) where
  contract : Node18Contract size Length Index

set_option maxHeartbeats 5000000 in
abbrev Node18Profile : Core.Residual.Focus.Profile Node17Stage.{u, v} :=
  Core.Residual.Focus.successor Node17Profile
    (fun (stage : Node16Stage.{u, v})
      (active : Node17Profile.{u, v}.Active stage) =>
        Node17Output stage active)

set_option maxHeartbeats 5000000 in
abbrev Node18Stage (Table : Type w) :=
  Core.Residual.Focus.Stage Node18Profile
    (fun (_stage : Node17Stage.{u, v})
      (_active : Node18Profile.Active _stage) => Node18Output Table)

noncomputable def node18 (table : Table) (previous : Node17Stage.{u, v}) :
    Node18Stage Table :=
  (Core.Residual.Focus.runCounted Node18Profile previous
    (fun _active _checks _exact =>
      (show Node18Output Table from { table := table }))).value

/-! Certified execution surface.  The opaque compatibility constructor above
is retained for generic fixtures; the production-facing constructor below
requires the complete Core certificate and stores that certificate in the
ledger payload. -/
abbrev Node18CertifiedStage (size : Nat) (Length : Type x) (Index : Type y) :=
  Core.Residual.Focus.Stage Node18Profile
    (fun (_stage : Node17Stage.{u, v})
      (_active : Node18Profile.Active _stage) =>
        Node18CertifiedOutput size Length Index)

noncomputable def node18Certified
    (contract : Node18Contract size Length Index)
    (previous : Node17Stage.{u, v}) :
    Node18CertifiedStage.{u, v, x, y} size Length Index :=
  (Core.Residual.Focus.runCounted Node18Profile previous
    (fun _active _checks _exact =>
      (show Node18CertifiedOutput size Length Index from
        { contract := contract }))).value

end HypostructureErdos64EG
