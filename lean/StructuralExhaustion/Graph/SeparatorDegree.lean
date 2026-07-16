import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.SeparatorDegree

universe u

variable {V : Type u} (object : FiniteObject V)

/-- Exact cubic/high split at one supplied separator of minimum degree three. -/
inductive Branch (vertex : V) : Type where
  | cubic (degree_eq : object.degree vertex = 3)
  | high (degree_ge : 4 ≤ object.degree vertex)

def classify (vertex : V) (degree_ge_three : 3 ≤ object.degree vertex) :
    Branch object vertex := by
  by_cases cubic : object.degree vertex = 3
  · exact .cubic cubic
  · exact .high (by omega)

/-- Only the supplied vertex degree is compared. -/
def checks : Nat := 1

end StructuralExhaustion.Graph.SeparatorDegree
