import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Closure
import Hypostructure.Core.Metadata
import HypostructureErdos64EG.Node6

/-!
# Diagram node 7: power-of-two-cycle terminal

Node 7 is exactly CT1's C1 terminal from node 6. It exposes the generated
power-of-two-cycle target as a direct Core closure and emits no successor.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- CT1's C1 constructor yields the exact public cycle target. -/
theorem node7_powerOfTwoCycle (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage)
    (isC1 : (node6RouteQuery.read stage active).terminal = .c1) :
    Target (node6ObjectQuery.read stage.previous active) :=
  CT1.FocusedCertificateEncoding.target_of_c1
    (node6RouteQuery.read stage active) isC1

/-- Node 7 closes directly with CT1's generated target certificate. -/
def node7 (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage)
    (isC1 : (node6RouteQuery.read stage active).terminal = .c1) :
    Core.Closure.Result
      (Target (node6ObjectQuery.read stage.previous active)) :=
  Core.Closure.Result.direct
    (.certificate (node7_powerOfTwoCycle stage active isC1))

/-- Node 7 uses Core's direct-certificate closure mechanism. -/
theorem node7_closure_mechanism (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage)
    (isC1 : (node6RouteQuery.read stage active).terminal = .c1) :
    (node7 stage active isC1).mechanism = Core.Closure.Mechanism.direct :=
  rfl

/-- Node 6's C1 route performed exactly one certificate validation. -/
theorem node7_route_checks_eq_one (stage : Node6Stage.{u})
    (active : Node6Focus.Active stage)
    (isC1 : (node6RouteQuery.read stage active).terminal = .c1) :
    (node6RouteQuery.read stage active).checks = 1 := by
  rw [(node6RouteQuery.read stage active).checks_eq_terminal, isC1]

/-- Node 7 is a terminal proof wrapper, so it performs no additional search. -/
def node7WorkBudget :
    Core.PolynomialCheckBudget Node6Stage.{u} :=
  Core.PolynomialCheckBudget.proofOnly Node6Stage.{u}

@[simp] theorem node7_checks_eq_zero (stage : Node6Stage.{u}) :
    node7WorkBudget.checks stage = 0 :=
  Core.PolynomialCheckBudget.proofOnly_checks _ _

/-- The proof-only terminal satisfies Core's zero-check polynomial budget. -/
theorem node7_work_bounded (stage : Node6Stage.{u}) :
    node7WorkBudget.checks stage <=
      node7WorkBudget.coefficient *
        (node7WorkBudget.size stage + 1) ^ node7WorkBudget.degree :=
  node7WorkBudget.bounded stage

/-- Proof-relevant audit record for node-7 direct terminal closure. -/
def node7Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node6Stage.{u} Node6Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node7", "node7"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node7", "node7_powerOfTwoCycle"⟩,
      .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node6", "node6"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node6", "node6RouteQuery"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := []
  frameworkSearch := [
    ⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.target_of_c1"⟩,
    ⟨"Hypostructure.Core.Closure", "Closure.Result.direct"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Closure", "Closure.Result"⟩,
      .closureResult⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.CT1.FocusedCertificate",
      "FocusedCertificateEncoding.target_of_c1"⟩,
    ⟨"Hypostructure.Core.Closure", "Closure.Result.direct"⟩,
    ⟨"Hypostructure.Core.Budget.Work",
      "PolynomialCheckBudget.proofOnly_checks"⟩
  ]
  closureMechanisms := [Core.Closure.Mechanism.direct]
  workBound := node7WorkBudget
  manualObligations := []

/-- Node 7 has no unrecorded mathematical or routing obligation. -/
def node7MetadataComplete :
    Core.Metadata.Complete node7Metadata :=
  ⟨rfl⟩

theorem node7_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node7Metadata.manualObligations) :=
  node7MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same zero-work bound used by the terminal. -/
theorem node7_metadata_work_bounded (stage : Node6Stage.{u}) :
    node7Metadata.workBound.checks stage <=
      node7Metadata.workBound.coefficient *
        (node7Metadata.workBound.size stage + 1) ^
          node7Metadata.workBound.degree :=
  node7MetadataComplete.work_bounded stage

#print axioms node7
#print axioms node7_powerOfTwoCycle
#print axioms node7_closure_mechanism
#print axioms node7_route_checks_eq_one
#print axioms node7_checks_eq_zero
#print axioms node7_work_bounded
#print axioms node7_metadata_has_no_manual_obligation
#print axioms node7_metadata_work_bounded

end HypostructureErdos64EG
