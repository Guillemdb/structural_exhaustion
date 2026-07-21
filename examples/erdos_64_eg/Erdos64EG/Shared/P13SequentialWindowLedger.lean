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

/-- The framework-owned exhaustive hot/cold view of the same accumulated
ledger.  This is the only legal branch interface for later Erdős nodes: the
hot constructor carries absence of rejected windows, while the cold
constructor exposes a rejected scheduled window without rebuilding routing
data. -/
noncomputable def p13AccumulatedHotColdOutcome {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :=
  (p13AccumulatedSequentialWindowLedger node18 bounded node21).hotColdOutcome

/-- On the framework hot constructor, every selected packing window is
retained by the unique accumulated ledger. -/
theorem p13AccumulatedHotCount_eq_packingCount {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded)
    (cold_empty :
      (p13AccumulatedSequentialWindowLedger node18 bounded node21).cold = []) :
    (p13AccumulatedSequentialWindowLedger node18 bounded node21).hot.length =
      p13 (Node21Context node18) := by
  have lengthExact :=
    (p13AccumulatedSequentialWindowLedger node18 bounded node21)
      |>.hot_length_eq_windows_length cold_empty
  change
    (p13AccumulatedSequentialWindowLedger node18 bounded node21).hot.length =
      (p13Windows (Node21Context node18)).length
  simpa [p13SequentialWeightedProfile] using lengthExact

/-- The single accumulated ledger also transports the distinguished original
target-avoiding completion.  Later curvature nodes retrieve this witness from
the same residual-owned value; they never manufacture terminal-fibre
nonemptiness. -/
noncomputable def p13AccumulatedOriginalCompletionWitness {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    P13OriginalCompletionWitness
      (p13AccumulatedFinalHotAggregate node18 bounded node21) :=
  (p13AccumulatedSequentialWindowLedger node18 bounded node21).finalWitness
    P13OriginalCompletionWitness
    p13SequentialTransportOriginalWitness
    (p13SequentialInitialOriginalWitness
      (Node21Context node18) node21.barrierRateCertificate)

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

/-- The accumulated framework hot/cold split carried by the sequential
ledger.  This proposition only says that the framework-owned ledger, final
aggregate, original witness, and exact split outcome are available from the
single accumulated residual.  It is deliberately not a hot-branch fact:
later nodes must inspect `Ledger.HotColdOutcome.hot` to obtain the
`cold = []` invariant. -/
structure P13AccumulatedHotColdSplitAvailable {V : Type u}
    (residual : InitialResidual V) : Prop where
  ledger : P13SequentialWindowLedgerAvailable residual
  aggregate :
    ∀ (node18 : Node18Stage residual)
      (bounded : Node19Low residual node18)
      (node21 : Node21Output node18 bounded),
        Nonempty (P13SequentialHotAggregate (Node21Context node18)
          node21.barrierRateCertificate)
  originalWitness :
    ∀ (node18 : Node18Stage residual)
      (bounded : Node19Low residual node18)
      (node21 : Node21Output node18 bounded),
        Nonempty (P13OriginalCompletionWitness
          (p13AccumulatedFinalHotAggregate node18 bounded node21))
  hotColdOutcome :
    ∀ (node18 : Node18Stage residual)
      (bounded : Node19Low residual node18)
      (node21 : Node21Output node18 bounded),
        Nonempty
          (Core.SequentialCompatibleExtensionLedger.Ledger.HotColdOutcome
            (p13AccumulatedSequentialWindowLedger node18 bounded node21))

theorem p13AccumulatedHotColdSplitAvailable {V : Type u}
    {residual : InitialResidual V} :
    P13AccumulatedHotColdSplitAvailable residual where
  ledger := p13SequentialWindowLedgerAvailable
  aggregate := by
    intro node18 bounded node21
    exact ⟨p13AccumulatedFinalHotAggregate node18 bounded node21⟩
  originalWitness := by
    intro node18 bounded node21
    exact ⟨p13AccumulatedOriginalCompletionWitness node18 bounded node21⟩
  hotColdOutcome := by
    intro node18 bounded node21
    exact ⟨p13AccumulatedHotColdOutcome node18 bounded node21⟩

/-- Framework hot branch consequence: if the accumulated split chooses the
hot constructor, all selected packing windows have been retained. -/
theorem p13AccumulatedHotCount_eq_packingCount_ofOutcome {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded)
    (outcome :
      Core.SequentialCompatibleExtensionLedger.Ledger.HotColdOutcome
        (p13AccumulatedSequentialWindowLedger node18 bounded node21))
    (isHot : ∃ cold_empty,
      outcome =
        Core.SequentialCompatibleExtensionLedger.Ledger.HotColdOutcome.hot
          (ledger := p13AccumulatedSequentialWindowLedger node18 bounded node21)
          cold_empty) :
    (p13AccumulatedSequentialWindowLedger node18 bounded node21).hot.length =
      p13 (Node21Context node18) := by
  rcases isHot with ⟨cold_empty, _⟩
  exact p13AccumulatedHotCount_eq_packingCount node18 bounded node21 cold_empty

/-- Register the compatible-extension computation once at its mathematical
producer.  Query resolution, branch preservation, and later transport are
all framework-owned. -/
instance node21StageEntailsSequentialWindowLedger {V : Type u} :
    Core.ResidualRefinement.State.StageEntails
      (@Node21Stage V) (@P13SequentialWindowLedgerAvailable V) where
  prove := fun _stage => p13SequentialWindowLedgerAvailable

instance node21StageEntailsAccumulatedHotColdSplit {V : Type u} :
    Core.ResidualRefinement.State.StageEntails
      (@Node21Stage V) (@P13AccumulatedHotColdSplitAvailable V) where
  prove := fun _stage => p13AccumulatedHotColdSplitAvailable

end Erdos64EG.Internal
