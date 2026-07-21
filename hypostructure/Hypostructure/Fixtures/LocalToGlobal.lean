import Hypostructure.Core.Assembly.LocalToGlobal

/-! # Pointwise local-to-global fixture -/

namespace Hypostructure.Fixtures.LocalToGlobal

open Hypostructure.Core

def problem : Core.Problem where
  Ambient := Nat
  Baseline _ := True
  BranchState _ := Unit

def semantics : Core.SemanticEquivalence problem :=
  Core.SemanticEquivalence.equality problem

def assembly : Core.AtomContextAssembly problem semantics where
  Interface := Nat
  Site _ := Unit
  interface object _ := object
  Atom interface := {value : Nat // value = interface}
  Context _ := Unit
  compatible _ _ := True
  atom object _ := ⟨object, rfl⟩
  context _ _ := ()
  assemble atom _ := atom.1
  extractedCompatible _ _ := trivial
  reconstruct _ _ := rfl

def localPair : assembly.LocalProperty :=
  fun {interface} atom _context => atom.1 = interface

def global (object : Nat) : Prop := object = object

def profile : assembly.LocalToGlobalProfile localPair global where
  close _object certificate := certificate.localAt ()

def certificate (object : Nat) : assembly.PointwiseCertificate localPair object where
  localAt _ := rfl

def root : Core.Residual.Ledger Nat :=
  Core.Residual.Ledger.initial 7

def closureNode := profile.node
  (fun previous : Core.Residual.Ledger Nat => previous.residual)
  (fun previous => certificate previous.residual)

def stage := closureNode.run root

example : stage.previous = root := rfl

example : global root.residual := stage.added

#print axioms Core.AtomContextAssembly.LocalToGlobalProfile.run
#print axioms Core.AtomContextAssembly.LocalToGlobalProfile.node
#print axioms stage

end Hypostructure.Fixtures.LocalToGlobal
