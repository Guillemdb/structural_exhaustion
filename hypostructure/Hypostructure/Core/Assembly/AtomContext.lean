import Hypostructure.Core.SemanticEquivalence

/-!
# Interface-indexed atom/context assembly

Domains register extraction, compatibility, assembly, and reconstruction.
Core owns replacement and semantic transport.
-/

namespace Hypostructure.Core

universe uAmbient uBranch uInterface uSite uAtom uContext

/-- Exact local/global decomposition indexed by a shared interface. -/
structure AtomContextAssembly
    (P : Problem.{uAmbient, uBranch}) (E : SemanticEquivalence P) where
  Interface : Type uInterface
  Site : P.Ambient -> Type uSite
  interface : (object : P.Ambient) -> Site object -> Interface
  Atom : Interface -> Type uAtom
  Context : Interface -> Type uContext
  compatible : {interface : Interface} ->
    Atom interface -> Context interface -> Prop
  atom : (object : P.Ambient) -> (site : Site object) ->
    Atom (interface object site)
  context : (object : P.Ambient) -> (site : Site object) ->
    Context (interface object site)
  assemble : {interface : Interface} ->
    Atom interface -> Context interface -> P.Ambient
  extractedCompatible : forall object site,
    compatible (atom object site) (context object site)
  reconstruct : forall object site,
    E.equivalent (assemble (atom object site) (context object site)) object

namespace AtomContextAssembly

variable {P : Problem.{uAmbient, uBranch}} {E : SemanticEquivalence P}

/-- A replacement atom certified compatible with the literal extracted
context at one site. -/
structure Replacement (A : AtomContextAssembly
    P E) (object : P.Ambient)
    (site : A.Site object) where
  atom : A.Atom (A.interface object site)
  compatible : A.compatible atom (A.context object site)

/-- Framework-owned local replacement in the exact extracted context. -/
def replace (A : AtomContextAssembly
    P E) {object : P.Ambient} {site : A.Site object}
    (replacement : A.Replacement object site) : P.Ambient :=
  A.assemble replacement.atom (A.context object site)

/-- Reconstruction preserves the baseline through registered semantics. -/
theorem reconstructedBaseline (A : AtomContextAssembly
    P E) (object : P.Ambient) (site : A.Site object)
    (baseline : P.Baseline object) :
    P.Baseline (A.assemble (A.atom object site) (A.context object site)) :=
  SemanticEquivalence.transport_baseline E
    (E.symm (A.reconstruct object site)) baseline

/-- Reconstruction preserves any target registered against the semantics. -/
theorem reconstructedTargetIff (A : AtomContextAssembly
    P E) {Target : P.Ambient -> Prop}
    (invariant : TargetInvariant E Target) (object : P.Ambient)
    (site : A.Site object) :
    Target (A.assemble (A.atom object site) (A.context object site)) <->
      Target object :=
  invariant.target_iff (A.reconstruct object site)

end AtomContextAssembly

end Hypostructure.Core
