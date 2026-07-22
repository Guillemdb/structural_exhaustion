import Hypostructure.Fixtures.GraphBasics
import Hypostructure.Graph.External
import Hypostructure.Graph.Target

/-!
# Graph external-boundary fixture

This fixture registers three local graph theorem contracts and a reviewed
exact-name allowlist.  It exercises the trust-boundary packaging without
introducing any graph-specific axiom or route.
-/

namespace Hypostructure.Fixtures.GraphExternal

open Hypostructure.Graph.External
open Hypostructure.Fixtures.GraphBasics

def k4VertexCountContract : LocalTheorem where
  source := ⟨"Hypostructure.Fixtures.GraphBasics", "k4_vertexCount"⟩
  hypotheses := True
  conclusion := k4.vertexCount = 4
  proof := fun _ => k4_vertexCount

def k4EdgeCountContract : LocalTheorem where
  source := ⟨"Hypostructure.Fixtures.GraphBasics", "k4_edgeCount"⟩
  hypotheses := True
  conclusion := k4.edgeCount = 6
  proof := fun _ => k4_edgeCount

def c4HasFourCycleContract : LocalTheorem where
  source := ⟨"Hypostructure.Fixtures.GraphBasics", "c4_has_four_cycle"⟩
  hypotheses := True
  conclusion := Hypostructure.Graph.HasCycleWithLength (fun length => length = 4) c4
  proof := fun _ => c4_has_four_cycle

def allowlist : Allowlist where
  sources := [
    k4VertexCountContract.source,
    k4EdgeCountContract.source,
    c4HasFourCycleContract.source
  ]

theorem k4VertexCountContract_conclusion :
    k4VertexCountContract.conclusion :=
  k4VertexCountContract.apply trivial

theorem k4EdgeCountContract_conclusion :
    k4EdgeCountContract.conclusion :=
  k4EdgeCountContract.apply trivial

theorem c4HasFourCycleContract_conclusion :
    c4HasFourCycleContract.conclusion :=
  c4HasFourCycleContract.apply trivial

theorem k4VertexCount_in_allowlist :
    allowlist.contains k4VertexCountContract.source := by
  simp [allowlist, Allowlist.contains]

theorem k4EdgeCount_in_allowlist :
    allowlist.contains k4EdgeCountContract.source := by
  simp [allowlist, Allowlist.contains]

theorem c4HasFourCycle_in_allowlist :
    allowlist.contains c4HasFourCycleContract.source := by
  simp [allowlist, Allowlist.contains]

end Hypostructure.Fixtures.GraphExternal
