import HypostructurePDEExamples.FiniteModel

/-!
# Additive local/tail decomposition

The example registers only primitive local and complementary pieces. The
framework constructs the atom/context assembly and owns reconstruction.
-/

namespace HypostructurePDEExamples.AdditiveLocalTail

open Hypostructure
open Hypostructure.PDE
open HypostructurePDEExamples.FiniteModel

local instance : Add problem.Ambient := by
  change Add Field
  infer_instance

def localPart (support : Finset Index) (field : Field) : Field :=
  fun index => if index ∈ support then field index else 0

def tailPart (support : Finset Index) (field : Field) : Field :=
  fun index => if index ∈ support then 0 else field index

def split : LocalTailAssembly problem where
  Localizer := Finset Index
  localPart := localPart
  tailPart := tailPart
  compatible := fun _ _ => True
  exact_reconstruction := by
    intro support field compatible
    change Field at field
    funext index
    change (if index ∈ support then field index else 0) +
      (if index ∈ support then 0 else field index) = field index
    by_cases member : index ∈ support
    · simp [member]
    · simp [member]

def assembly : Core.AtomContextAssembly problem equalitySemantics :=
  split.toCoreAssembly equalitySemantics

def support : Finset Index := {0, 1}

def site (field : Field) : assembly.Site field :=
  Subtype.mk support trivial

theorem reconstructs (field : Field) :
    assembly.assemble
        (assembly.atom field (site field))
        (assembly.context field (site field)) = field :=
  assembly.reconstruct field (site field)

theorem local_vanishes_off_support (field : Field) (index : Index)
    (outside : index ∉ support) :
    assembly.atom field (site field) index = 0 := by
  change (if index ∈ support then field index else 0) = 0
  simp [outside]

theorem tail_vanishes_on_support (field : Field) (index : Index)
    (inside : index ∈ support) :
    assembly.context field (site field) index = 0 := by
  change (if index ∈ support then 0 else field index) = 0
  simp [inside]

#print axioms reconstructs
#print axioms local_vanishes_off_support
#print axioms tail_vanishes_on_support

end HypostructurePDEExamples.AdditiveLocalTail
