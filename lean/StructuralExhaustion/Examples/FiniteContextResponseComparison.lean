import StructuralExhaustion.Graph.FiniteContextResponseComparison

namespace StructuralExhaustion.Examples.FiniteContextResponseComparison

open StructuralExhaustion

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ ↦ True
  rank := fun _ ↦ 0
  BranchState := fun _ ↦ Unit

def branch : Core.BranchContext problem := ⟨(), trivial, ()⟩

def response (object code : Bool) : Bool := object && code

def profile (left right : Bool) :
    Graph.FiniteContextResponseComparison.Profile problem branch where
  Object := Bool
  Outside := Bool
  Code := Bool
  codes := Core.Enumeration.bool
  left := left
  right := right
  response := response
  targetResponse := fun object outside ↦ response object outside = true
  decode := id
  response_reflect := by intro object code; rfl
  pairCoverage := by intro outside; exact ⟨outside, Iff.rfl, Iff.rfl⟩

example : Nonempty ((profile true false).Distinction) := by
  refine ⟨⟨true, true, rfl, ?_⟩⟩
  simp [profile, response]

example : (profile true true).Neutrality := by
  refine ⟨fun _ ↦ rfl, fun _ ↦ Iff.rfl⟩

example : (profile true false).ct7Run.outcome.Valid :=
  (profile true false).ct7Run_verified

example : (profile true false).checks = 4 := by
  native_decide

end StructuralExhaustion.Examples.FiniteContextResponseComparison
