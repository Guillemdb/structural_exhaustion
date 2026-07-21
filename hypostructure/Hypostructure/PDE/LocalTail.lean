import Hypostructure.Core.Assembly.AtomContext
import Hypostructure.PDE.Representation

/-!
# Exact additive local/tail assembly
-/

namespace Hypostructure.PDE

universe u

/--
Primitive local/tail data. Reconstruction is literal equality; Core owns the
resulting atom/context assembly and its execution interfaces.
-/
structure LocalTailAssembly (P : Core.Problem.{u, u}) [Add P.Ambient] where
  Localizer : Type u
  localPart : Localizer -> P.Ambient -> P.Ambient
  tailPart : Localizer -> P.Ambient -> P.Ambient
  compatible : Localizer -> P.Ambient -> Prop
  exact_reconstruction : forall (localizer : Localizer) (G : P.Ambient),
    compatible localizer G ->
      localPart localizer G + tailPart localizer G = G

namespace LocalTailAssembly

/-- Register exact additive splitting as Core atom/context assembly. -/
def toCoreAssembly {P : Core.Problem.{u, u}} [Add P.Ambient]
    (A : LocalTailAssembly P) (S : RepresentationSemantics P) :
    Core.AtomContextAssembly P S where
  Interface := A.Localizer
  Site := fun object => {localizer : A.Localizer // A.compatible localizer object}
  interface := fun _ site => site.1
  Atom := fun _ => P.Ambient
  Context := fun _ => P.Ambient
  compatible := fun {localizer} atomPart tail =>
    Exists fun object =>
      A.compatible localizer object ∧
      atomPart = A.localPart localizer object ∧
      tail = A.tailPart localizer object
  atom := fun object site => A.localPart site.1 object
  context := fun object site => A.tailPart site.1 object
  assemble := fun atom context => atom + context
  extractedCompatible := fun object site =>
    ⟨object, site.2, rfl, rfl⟩
  reconstruct := by
    intro object site
    rw [A.exact_reconstruction site.1 object site.2]

end LocalTailAssembly

end Hypostructure.PDE
