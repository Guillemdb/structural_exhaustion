import StructuralExhaustion.Graph.HighCenterPort

namespace StructuralExhaustion.Graph.FanCertificateRequirement

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V) (center : V)

/-!
# First fan-certificate requirement

A fan certificate begins with one label for every actual incident port. This
module identifies the first such request from the declared neighbour order.
It does not enumerate a label universe, accept an attachment map, or assert
that the requested label is absent.
-/

def firstPort (centerHigh : 4 ≤ object.degree center) :
    HighCenterPort.Port object center :=
  ⟨0, by
    have positive : 0 < object.degree center := lt_of_lt_of_le (by decide) centerHigh
    have lengthEq :
        (object.input.orderedNeighbors center).values.length = object.degree center := by
      simpa [FiniteObject.degree] using object.input.orderedNeighbors_length center
    rw [lengthEq]
    exact positive⟩

/-- Exact first obligation in the marked-fan certificate schedule. -/
structure FirstLabelRequest (centerHigh : 4 ≤ object.degree center) where
  port : HighCenterPort.Port object center
  portExact : port = firstPort object center centerHigh
  endpoint : V
  endpointExact : endpoint = HighCenterPort.endpoint object center port

def firstLabelRequest (centerHigh : 4 ≤ object.degree center) :
    FirstLabelRequest object center centerHigh where
  port := firstPort object center centerHigh
  portExact := rfl
  endpoint := HighCenterPort.endpoint object center (firstPort object center centerHigh)
  endpointExact := rfl

theorem firstLabelRequest_port_index (centerHigh : 4 ≤ object.degree center) :
    (firstLabelRequest object center centerHigh).port.1 = 0 :=
  rfl

def visibleChecks : Nat := 0

theorem visibleChecks_eq_zero : visibleChecks = 0 := rfl

end StructuralExhaustion.Graph.FanCertificateRequirement
