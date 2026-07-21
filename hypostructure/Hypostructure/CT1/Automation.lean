import Hypostructure.CT1.Theorems
import Hypostructure.CT1.Certificate
import Hypostructure.CT1.FocusedCertificate

/-!
# CT1 public automation surface

Applications provide a `Spec`, a `Capability`, and the literal predecessor.
The framework owns schedule retrieval, search, routing, ledger extension,
terminal selection, tracing, and work accounting.
-/

namespace Hypostructure.CT1

universe uPrevious uCandidate

/-- Public evidence-carrying CT1 executor. -/
def execute {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCandidate} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  run spec capability previous

/-- Public proof-carrying CT1 executor.  The framework classically chooses the
public target or exact avoidance branch and owns the resulting ledger stage. -/
noncomputable def executePublicTarget {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCandidate}
      Previous PublicTarget)
    (previous : Previous) : CertificateEncoding.ExecutionResult encoding :=
  encoding.runPublicTarget previous

/-- Close an impossible C1 arm and return the exact avoiding successor while
preserving the complete CT1 predecessor ledger. -/
def closeC1ContinueAvoiding {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCandidate}
      Previous PublicTarget)
    (stage : CertificateEncoding.Stage encoding)
    (targetImpossible : Not (PublicTarget stage.previous)) :
    CertificateEncoding.AvoidingSuccessorStage encoding :=
  encoding.continueAvoiding stage targetImpossible

syntax (name := ct1Execute) "ct1_execute " term " using " term : term

macro_rules
  | `(ct1_execute $previous:term using $capability:term) =>
      `(Hypostructure.CT1.execute _ $capability $previous)

syntax (name := ct1Verified) "ct1_verified " term " using " term : tactic

macro_rules
  | `(tactic| ct1_verified $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT1.run_verified _ $capability $previous)

syntax (name := ct1Total) "ct1_total " term " using " term : tactic

macro_rules
  | `(tactic| ct1_total $previous:term using $capability:term) =>
      `(tactic| exact Hypostructure.CT1.run_total _ $capability $previous)

end Hypostructure.CT1
