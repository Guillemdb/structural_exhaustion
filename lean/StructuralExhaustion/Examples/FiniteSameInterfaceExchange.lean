import StructuralExhaustion.Graph.FiniteSameInterfaceExchange
import StructuralExhaustion.Graph.FiniteSameInterfacePackedBoundary
import Mathlib.Tactic

namespace StructuralExhaustion.Examples.FiniteSameInterfaceExchange

open StructuralExhaustion

structure Piece where
  responseTag : Bool
  size : Nat

def source : Piece := ⟨false, 2⟩
def replacement : Piece := ⟨false, 1⟩

noncomputable def representatives :=
  Graph.FiniteSameInterfaceExchange.Representatives.exact
    source replacement Piece.size

theorem increment_exact : representatives.increment = 1 := by
  norm_num [representatives,
    Graph.FiniteSameInterfaceExchange.Representatives.exact,
    source, replacement]

noncomputable def boundary :
    Graph.FiniteSameInterfaceExchange.BoundaryCompatible representatives where
  Profile := Unit
  profile := fun _ => ()
  equal := rfl

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def branch : Core.BranchContext problem := ⟨(), trivial, ()⟩

noncomputable def table :
    Graph.FiniteSameInterfaceExchange.ResponseTable representatives where
  Outside := Bool
  Code := Bool
  codes := Core.Enumeration.bool
  decode := id
  targetResponseReplacement := fun outside => replacement.responseTag = outside
  targetResponseSource := fun outside => source.responseTag = outside
  replacementResponse := fun code => decide (replacement.responseTag = code)
  sourceResponse := fun code => decide (source.responseTag = code)
  replacementReflect := by intro code; simp
  sourceReflect := by intro code; simp
  coverage := by
    intro outside
    exact ⟨outside, by simp, by simp⟩

theorem finite_checks :
    (table.comparisonProfile (P := problem) (branch := branch)).checks = 4 := by
  rw [table.checks_eq]
  rfl

/-- The symbolic universal-response constructor materializes only the two
Boolean truth codes and never scans the outside type. -/
noncomputable def universalTable :
    Graph.FiniteSameInterfaceExchange.ResponseTable representatives := by
  let replacementTarget := fun outside : Bool =>
    replacement.responseTag = outside
  let sourceTarget := fun outside : Bool => source.responseTag = outside
  exact Graph.FiniteSameInterfaceExchange.ResponseTable.ofUniversal Bool
    replacementTarget sourceTarget (by intro outside; simp [replacementTarget,
      sourceTarget, replacement, source])

theorem universal_table_checks :
    (universalTable.comparisonProfile
      (P := problem) (branch := branch)).checks = 4 := by
  rw [universalTable.checks_eq]
  rfl

theorem universal_table_coverage (outside : Bool) :
    ∃ code,
      (universalTable.targetResponseReplacement outside ↔
        universalTable.replacementResponse code = true) ∧
      (universalTable.targetResponseSource outside ↔
        universalTable.sourceResponse code = true) :=
  universalTable.coverage outside

noncomputable def silent :
    Graph.FiniteSameInterfaceExchange.ConditionalSilent
      representatives boundary table where
  Silent := Unit
  orient := fun _changing _complete => ()

theorem exact_response_reflection (code : Bool) :
    table.sourceResponse code = true ↔
      table.targetResponseSource (table.decode code) :=
  table.sourceReflect code

namespace PackedBoundaryProfileFixture

open Graph.FiniteSameInterfaceExchange.PackedBoundary

variable {input : Graph.PackedMinimumDegreeCycle.StaticInput}
variable {T : Type} {boundaries : FinEnum T} [Nonempty T]
variable {ctx :
  Core.MinimalCounterexampleContext input.problem input.Target}
variable {atom :
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom
    input boundaries ctx}
variable {CodePiece : Type}
variable {representatives :
  Graph.FiniteSameInterfaceExchange.Representatives CodePiece}
variable {boundary :
  Graph.FiniteSameInterfaceExchange.BoundaryCompatible representatives}
variable {table :
  Graph.FiniteSameInterfaceExchange.ResponseTable representatives}

/-- Non-Erdős API fixture: a problem supplies one closure certificate, and
the graph framework constructs the packed-boundary silent exchange. -/
noncomputable def packedSilentExchange
    (certificate :
      MinimumDegreeCycleReplacement.ClosureCertificate
        input boundaries atom representatives table boundary) :
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.SilentExchange
      input boundaries atom :=
  MinimumDegreeCycleReplacement.ClosureCertificate.silentExchange certificate

/-- Non-Erdős closure fixture for the same public profile API. -/
theorem packedProfile_closes
    (certificate :
      MinimumDegreeCycleReplacement.ClosureCertificate
        input boundaries atom representatives table boundary) :
    False :=
  MinimumDegreeCycleReplacement.ClosureCertificate.impossible certificate

end PackedBoundaryProfileFixture

#print axioms increment_exact
#print axioms finite_checks
#print axioms exact_response_reflection
#print axioms universal_table_checks
#print axioms universal_table_coverage
#print axioms PackedBoundaryProfileFixture.packedProfile_closes

end StructuralExhaustion.Examples.FiniteSameInterfaceExchange
