import Hypostructure.Graph.RootedReturn
import HypostructureErdos64EG.Node4

/-!
# Diagram node 5: edge-rooted target algebra

Graph owns the return/cycle dictionary and Core owns focused continuation.
The EG application supplies only the Mersenne instance of the generic shifted
length predicate.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- The paper's Mersenne return predicate as a direct graph API instance. -/
def mersenneReturnAlgebra :
    Graph.RootedReturnTargetAlgebra PowerOfTwoLength where
  ReturnLengthOK := MersenneLength
  returnLengthOK_iff_shifted := fun _length => Iff.rfl

/-- The sole payload established by node 5. -/
abbrev Node5Output (stage : Node4Stage.{u})
    (active : Node4Focus.Active stage) :=
  mersenneReturnAlgebra.AvoidanceCertificate
    (node4ContextQuery.read stage active).G

/-- Exact accumulated stage after node 5. -/
abbrev Node5Stage :=
  Core.Residual.Focus.Stage Node4Focus Node5Output

/-- Graph derives rooted-return avoidance from inherited target avoidance;
Core performs all branch inspection and ledger extension. -/
noncomputable def node5 (previous : Node4Stage.{u}) : Node5Stage.{u} :=
  Core.Residual.Focus.run Node4Focus previous fun active =>
    let minimal := node4ContextQuery.read previous active
    mersenneReturnAlgebra.avoidanceCertificate minimal.G minimal.avoids

/-- Focus inherited by node 6 and later counterexample nodes. -/
abbrev Node5Focus :=
  Core.Residual.Focus.successor Node4Focus Node5Output

/-- Typed query for node 5's exact graph-owned certificate. -/
def node5CertificateQuery :
    Core.Residual.Focus.ActiveQuery Node5Focus
      (fun stage active => Node5Output stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

/-- The minimal context query lifted through node 5 without copying it. -/
def node4ContextAtNode5Query :
    Core.Residual.Focus.ActiveQuery Node5Focus
      (fun stage active => Node4Output stage.previous.previous active) :=
  node4ContextQuery.preserve

@[simp] theorem node5_previous (previous : Node4Stage.{u}) :
    (node5 previous).previous = previous :=
  rfl

/-- The target/return equivalence remains graph-owned. -/
theorem node5_target_iff_rootedReturn
    (stage : Node4Stage.{u}) (active : Node4Focus.Active stage) :
    Target (node4ContextQuery.read stage active).G <->
      mersenneReturnAlgebra.HasRootedReturn
        (node4ContextQuery.read stage active).G :=
  mersenneReturnAlgebra.target_iff_hasRootedReturn _

#print axioms node5
#print axioms node5_target_iff_rootedReturn

end HypostructureErdos64EG
