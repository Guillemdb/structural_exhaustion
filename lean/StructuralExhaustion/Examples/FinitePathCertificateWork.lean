import StructuralExhaustion.Graph.FinitePathCertificateWork

namespace StructuralExhaustion.Examples.FinitePathCertificateWork

open StructuralExhaustion.Graph

universe u v

/-! A problem-independent fixture for the path-certificate work ledger. -/

example {V : Type u} (vertices : FinEnum V) {G : SimpleGraph V}
    {start finish : V} (path : G.Walk start finish) (isPath : path.IsPath) :
    path.length ≤ vertices.card :=
  Graph.FinitePathCertificateWork.pathLength_le_vertices
    vertices path isPath

example {A : Type v} (schedule : List A) (cost : A → Nat) (cap slots : Nat)
    (costLe : ∀ item ∈ schedule, cost item ≤ cap)
    (lengthLe : schedule.length ≤ slots) :
    Graph.FinitePathCertificateWork.scheduledChecks schedule cost ≤
      slots * (cap + 1) :=
  Graph.FinitePathCertificateWork.scheduledChecks_le_of_length_le
    schedule cost cap slots costLe lengthLe

end StructuralExhaustion.Examples.FinitePathCertificateWork
