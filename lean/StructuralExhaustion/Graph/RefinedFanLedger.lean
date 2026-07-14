import StructuralExhaustion.Graph.CertificateClosedFanCandidate
import StructuralExhaustion.Graph.HybridFanCandidate

namespace StructuralExhaustion.Graph.RefinedFanLedger

universe u

/-! Common ordinary-reserve data for refined fan ledgers. -/

structure Reserve (Vertex : Type u) where
  VertexUsed : Vertex → Prop
  vertexUsedDecidable : ∀ vertex, Decidable (VertexUsed vertex)
  IncidenceUsed : FanClosedPort.LocalCarrier Vertex → Prop
  incidenceUsedDecidable : ∀ incidence, Decidable (IncidenceUsed incidence)

namespace Reserve

def vertexReserve (reserve : Reserve Vertex) :
    CertificateClosedFanCandidate.VertexReserve Vertex where
  Used := reserve.VertexUsed
  usedDecidable := reserve.vertexUsedDecidable

def incidenceReserve (reserve : Reserve Vertex) :
    HybridFanCandidate.IncidenceReserve Vertex where
  Used := reserve.IncidenceUsed
  usedDecidable := reserve.incidenceUsedDecidable

end Reserve

end StructuralExhaustion.Graph.RefinedFanLedger
