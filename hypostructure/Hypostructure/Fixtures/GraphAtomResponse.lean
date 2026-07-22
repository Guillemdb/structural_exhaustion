import Hypostructure.Fixtures.GraphBoundariedAtom
import Hypostructure.Graph.AtomResponse

/-!
# Arbitrary atom-response coordinate fixture

The coordinate carrier below consists of three different kinds of local
response data.  None of them is definitionally a graph piece.  The system
registers them in the exact boundary-degree fibre generated for the existing
proper triangle atom and gives each its literal all-context target semantics.
The framework then constructs the exact target-complete quotient.
-/

namespace Hypostructure.Fixtures.GraphAtomResponse

open Hypostructure.Graph
open Hypostructure.Graph.AtomResponse

/-- Heterogeneous local response-coordinate names of the kind quantified over
by the original graph definition. -/
inductive Coordinate where
  | terminalTrace
  | rootedReturn
  | curvatureTest

/-- An arbitrary coordinate collection attached to the exact atom certificate.
For this finite fixture all three coordinates record the source atom's literal
target response, so the exact quotient identifies them. -/
noncomputable def system : CoordinateSystem
    Hypostructure.Fixtures.GraphBoundariedAtom.certificate
    Hypostructure.Fixtures.GraphBoundariedAtom.Target where
  Coordinate := Coordinate
  boundaryDegreeProfile := fun _coordinate =>
    Hypostructure.Fixtures.GraphBoundariedAtom.certificate.boundaryDegreeProfile
  realize := fun _coordinate outside =>
    Graph.glue Hypostructure.Fixtures.GraphBoundariedAtom.piece outside
  in_registered_fibre := fun _coordinate => rfl

/-- Framework-generated maximal target-complete quotient. -/
noncomputable def quotient := system.exactQuotient

theorem trace_identified_with_return :
    quotient.Identified .terminalTrace .rootedReturn := by
  intro outside
  rfl

theorem trace_contextUniversal :
    system.ContextEquivalent .terminalTrace .rootedReturn :=
  quotient.contextUniversal_of_identified trace_identified_with_return

theorem trace_profile_is_registered :
    system.boundaryDegreeProfile .terminalTrace =
      Hypostructure.Fixtures.GraphBoundariedAtom.certificate.boundaryDegreeProfile :=
  system.in_registered_fibre .terminalTrace

theorem identified_profiles_equal :
    system.boundaryDegreeProfile .terminalTrace =
      system.boundaryDegreeProfile .rootedReturn :=
  quotient.profile_preserved trace_identified_with_return

/-! A second system checks that arbitrary coordinates may have genuinely
different target responses, rather than merely different names. -/

def SizeTarget (object : FiniteObject) : Prop :=
  object.vertexCount =
    Hypostructure.Fixtures.GraphBoundariedAtom.ambient.vertexCount

noncomputable def varyingSystem : CoordinateSystem
    Hypostructure.Fixtures.GraphBoundariedAtom.certificate SizeTarget where
  Coordinate := Coordinate
  boundaryDegreeProfile := fun _coordinate =>
    Hypostructure.Fixtures.GraphBoundariedAtom.certificate.boundaryDegreeProfile
  realize
    | .terminalTrace, _outside =>
        Hypostructure.Fixtures.GraphBoundariedAtom.ambient
    | .rootedReturn, _outside | .curvatureTest, _outside =>
        Hypostructure.Fixtures.GraphBoundariedAtom.piece.pack
  in_registered_fibre := fun _coordinate => rfl

theorem varying_responses_distinguished :
    Not (varyingSystem.ContextEquivalent .terminalTrace .rootedReturn) := by
  intro equivalent
  have targetAtSource :
      SizeTarget Hypostructure.Fixtures.GraphBoundariedAtom.ambient :=
    rfl
  have targetAtReturn :=
    (equivalent Hypostructure.Fixtures.GraphBoundariedAtom.outside).mp
      targetAtSource
  change
    Hypostructure.Fixtures.GraphBoundariedAtom.piece.pack.vertexCount =
      Hypostructure.Fixtures.GraphBoundariedAtom.ambient.vertexCount at targetAtReturn
  rw [Hypostructure.Fixtures.GraphBoundariedAtom.piece_vertexCount,
    Hypostructure.Fixtures.GraphBoundariedAtom.ambient_vertexCount] at targetAtReturn
  omega

theorem varying_exact_quotient_does_not_identify :
    Not (varyingSystem.exactQuotient.Identified
      .terminalTrace .rootedReturn) :=
  varying_responses_distinguished

/-- The quotient type is generated from exact all-context response semantics,
not from a fixture-authored routing or equivalence proof. -/
abbrev QuotientFixture := quotient.Carrier

#print axioms CoordinateSystem.exactSetoid
#print axioms CoordinateSystem.exactQuotient
#print axioms TargetCompleteQuotient.profile_preserved
#print axioms TargetCompleteQuotient.contextUniversal_of_identified
#print axioms trace_identified_with_return
#print axioms trace_contextUniversal
#print axioms trace_profile_is_registered
#print axioms identified_profiles_equal
#print axioms varying_responses_distinguished
#print axioms varying_exact_quotient_does_not_identify

end Hypostructure.Fixtures.GraphAtomResponse
