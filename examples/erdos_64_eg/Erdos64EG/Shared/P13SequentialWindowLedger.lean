import Erdos64EG.Node21
import Erdos64EG.Future.P13SequentialWeightedHotColdLedger
import StructuralExhaustion.Core.CachedWitness

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Framework-ledger exposure of the sequential hot/cold window computation

The actual accept/reject decisions and aggregate transport are performed by
`Core.SequentialCompatibleExtensionLedger`.  This module only registers the
resulting residual-indexed value as a fact entailed by node [21], so later
paper nodes retrieve it from the one accumulated ledger.
-/

/-- Node [21]'s exact selected graph and rate certificate determine one
framework-owned sequential compatible-extension ledger. -/
def P13SequentialWindowLedgerAvailable {V : Type u}
    (residual : InitialResidual V) : Prop :=
  ∀ (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded),
      Nonempty (P13SequentialWeightedLedger (Node21Context node18)
        node21.barrierRateCertificate)

theorem p13SequentialWindowLedgerAvailable {V : Type u}
    {residual : InitialResidual V} :
    P13SequentialWindowLedgerAvailable residual := by
  intro node18 bounded node21
  exact ⟨p13SequentialWeightedLedger (Node21Context node18)
    node21.barrierRateCertificate⟩

/-! ## Canonical value of the accumulated compatible-extension ledger

The sequential runner is determined entirely by the incoming residual.  The
framework caches that value once and every later CT reads the same final
aggregate.  In particular, node [31] and node [49] cannot accidentally count
different completion carriers.
-/

/-- The one cached sequential ledger determined by node [21]'s residual. -/
noncomputable def p13AccumulatedSequentialWindowLedger {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    P13SequentialWeightedLedger (Node21Context node18)
      node21.barrierRateCertificate :=
  Core.cachedValue
    (p13SequentialWeightedLedger (Node21Context node18)
      node21.barrierRateCertificate)

/-- Caching changes no mathematical value. -/
theorem p13AccumulatedSequentialWindowLedger_eq {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    p13AccumulatedSequentialWindowLedger node18 bounded node21 =
      p13SequentialWeightedLedger (Node21Context node18)
        node21.barrierRateCertificate :=
  Core.cachedValue_eq _

/-- The literal final hot aggregate read from the single accumulated ledger. -/
noncomputable def p13AccumulatedFinalHotAggregate {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    P13SequentialHotAggregate (Node21Context node18)
      node21.barrierRateCertificate :=
  (p13AccumulatedSequentialWindowLedger node18 bounded node21).finalAggregate

/-- The accumulated final aggregate is the existing sequential final value. -/
theorem p13AccumulatedFinalHotAggregate_eq {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    p13AccumulatedFinalHotAggregate node18 bounded node21 =
      p13SequentialFinalHotAggregate (Node21Context node18)
        node21.barrierRateCertificate := by
  exact congrArg (fun ledger => ledger.finalAggregate)
    (p13AccumulatedSequentialWindowLedger_eq node18 bounded node21)

/-- Register the compatible-extension computation once at its mathematical
producer.  Query resolution, branch preservation, and later transport are
all framework-owned. -/
instance node21StageEntailsSequentialWindowLedger {V : Type u} :
    Core.ResidualRefinement.State.StageEntails
      (@Node21Stage V) (@P13SequentialWindowLedgerAvailable V) where
  prove := fun _stage => p13SequentialWindowLedgerAvailable

end Erdos64EG.Internal
