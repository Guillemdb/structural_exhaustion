import StructuralExhaustion.Graph.WalkTypeAD5Projection
import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.Graph.TypeAFullD5Signature

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)

/-!
# The complete labelled D5 signature at its producer boundary

The first seven summands below are the D5 coordinates determined by a Type-A
support and the canonical anchored return supplied for every completion port.
They are deliberately separate summands: equal numerical observations never
identify, for example, a connector length with a trace position.

Receiver-entry channels and the later band, theta, silent-basin and carrier
coordinates are not consequences of bridgelessness alone.  The manuscript
introduces them only after the corresponding receiver-entry or saturated
route-8 producer.  `Pending` records that exact origin instead of importing a
downstream conclusion into the base D5 state.
-/

abbrev Cubic := profile.Cubic object
abbrev TraceIncidence := TypeATraceIncidenceCoordinate.Coordinate object profile
abbrev Port := TypeACompletionPortCoordinate.Coordinate object profile
abbrev ReturnProducer := TypeAAnchoredReturnCoordinate.Producer object profile

/-- Seven distinct base labels in the order in which the paper declares them:
canonical trace, trace incidence, completion port, canonical return, first
entry, connector path, and connector length. -/
abbrev BaseCoordinate :=
  Cubic object profile ⊕
  TraceIncidence object profile ⊕
  Port object profile ⊕
  Port object profile ⊕
  Port object profile ⊕
  Port object profile ⊕
  Port object profile

/-- The seven mutually disjoint clause tags of the locally available D5
signature.  This is deliberately separate from the coordinate payload: the
uniform cut code retains both the clause kind and its exact local label. -/
inductive BaseKind
  | canonicalTrace
  | traceIncidence
  | completionPort
  | canonicalReturn
  | firstEntryReceiver
  | connectorPath
  | connectorLength
  deriving DecidableEq, Repr, Fintype

/-- Exact graph-level labels of the seven base coordinate families.  These
labels identify coordinates, whereas `BaseValue` records their observed
response data. -/
inductive BaseLabel
  | canonicalTrace (source : V)
  | traceIncidence (source : V) (position : Nat)
  | completionPort (receiver outside : V)
  | canonicalReturn (receiver outside : V)
  | firstEntryReceiver (receiver outside : V)
  | connectorPath (receiver outside : V)
  | connectorLength (receiver outside : V)

@[implicit_reducible]
noncomputable def baseCoordinates : FinEnum (BaseCoordinate object profile) := by
  letI : FinEnum (Cubic object profile) := SupportProfile.cubics object profile
  letI : FinEnum (TraceIncidence object profile) :=
    TypeATraceIncidenceCoordinate.coordinates object profile
  letI : FinEnum (Port object profile) :=
    TypeACompletionPortCoordinate.coordinates object profile
  exact inferInstance

namespace BaseCoordinate

def kind : BaseCoordinate object profile → BaseKind
  | .inl _ => .canonicalTrace
  | .inr (.inl _) => .traceIncidence
  | .inr (.inr (.inl _)) => .completionPort
  | .inr (.inr (.inr (.inl _))) => .canonicalReturn
  | .inr (.inr (.inr (.inr (.inl _)))) => .firstEntryReceiver
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .connectorPath
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .connectorLength

noncomputable def label : BaseCoordinate object profile → BaseLabel (V := V)
  | .inl cubic => .canonicalTrace cubic.1.1
  | .inr (.inl incidence) => .traceIncidence
      (incidence.source object profile).1.1
      (incidence.position object profile)
  | .inr (.inr (.inl port)) => .completionPort
      (port.receiver object profile).1 (port.outside object profile)
  | .inr (.inr (.inr (.inl port))) => .canonicalReturn
      (port.receiver object profile).1 (port.outside object profile)
  | .inr (.inr (.inr (.inr (.inl port)))) => .firstEntryReceiver
      (port.receiver object profile).1 (port.outside object profile)
  | .inr (.inr (.inr (.inr (.inr (.inl port))))) => .connectorPath
      (port.receiver object profile).1 (port.outside object profile)
  | .inr (.inr (.inr (.inr (.inr (.inr port))))) => .connectorLength
      (port.receiver object profile).1 (port.outside object profile)

def canonicalTrace (cubic : Cubic object profile) : BaseCoordinate object profile :=
  .inl cubic

def traceIncidence (coordinate : TraceIncidence object profile) :
    BaseCoordinate object profile := .inr (.inl coordinate)

def completionPort (port : Port object profile) : BaseCoordinate object profile :=
  .inr (.inr (.inl port))

def canonicalReturn (port : Port object profile) : BaseCoordinate object profile :=
  .inr (.inr (.inr (.inl port)))

def firstEntryReceiver (port : Port object profile) : BaseCoordinate object profile :=
  .inr (.inr (.inr (.inr (.inl port))))

def connectorPath (port : Port object profile) : BaseCoordinate object profile :=
  .inr (.inr (.inr (.inr (.inr (.inl port)))))

def connectorLength (port : Port object profile) : BaseCoordinate object profile :=
  .inr (.inr (.inr (.inr (.inr (.inr port)))))

/-- The exact family label identifies the underlying D5 coordinate. -/
theorem label_injective :
    Function.Injective (label object profile) := by
  intro left right equal
  rcases left with cubic | (incidence | (port | (returned | (entry | (path | length)))))
  · rcases right with other | (other | (other | (other | (other | (other | other)))))
    · simp only [label, BaseLabel.canonicalTrace.injEq] at equal
      have cubicEqual : cubic = other := by
        apply Subtype.ext
        apply Subtype.ext
        exact equal
      subst other
      rfl
    all_goals contradiction
  · rcases right with other | (other | (other | (other | (other | (other | other)))))
    · contradiction
    · simp only [label, BaseLabel.traceIncidence.injEq] at equal
      have incidenceEqual : incidence = other := by
        rcases incidence with ⟨cubic, position⟩
        rcases other with ⟨otherCubic, otherPosition⟩
        simp only [TypeATraceIncidenceCoordinate.Coordinate.source,
          TypeATraceIncidenceCoordinate.Coordinate.position] at equal
        have cubicEqual : cubic = otherCubic := by
          apply Subtype.ext
          apply Subtype.ext
          exact equal.1
        subst otherCubic
        have positionEqual : position = otherPosition := Fin.ext equal.2
        subst otherPosition
        rfl
      subst other
      rfl
    all_goals contradiction
  · rcases right with other | (other | (other | (other | (other | (other | other)))))
    · contradiction
    · contradiction
    · simp only [label, BaseLabel.completionPort.injEq] at equal
      have portEqual : port = other := by
        apply TypeACompletionPortCoordinate.Coordinate.ext object profile
        · apply Subtype.ext
          exact equal.1
        · exact equal.2
      subst other
      rfl
    all_goals contradiction
  · rcases right with other | (other | (other | (other | (other | (other | other)))))
    · contradiction
    · contradiction
    · contradiction
    · simp only [label, BaseLabel.canonicalReturn.injEq] at equal
      have portEqual : returned = other := by
        apply TypeACompletionPortCoordinate.Coordinate.ext object profile
        · apply Subtype.ext
          exact equal.1
        · exact equal.2
      subst other
      rfl
    all_goals contradiction
  · rcases right with other | (other | (other | (other | (other | (other | other)))))
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · simp only [label, BaseLabel.firstEntryReceiver.injEq] at equal
      have portEqual : entry = other := by
        apply TypeACompletionPortCoordinate.Coordinate.ext object profile
        · apply Subtype.ext
          exact equal.1
        · exact equal.2
      subst other
      rfl
    all_goals contradiction
  · rcases right with other | (other | (other | (other | (other | (other | other)))))
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · simp only [label, BaseLabel.connectorPath.injEq] at equal
      have portEqual : path = other := by
        apply TypeACompletionPortCoordinate.Coordinate.ext object profile
        · apply Subtype.ext
          exact equal.1
        · exact equal.2
      subst other
      rfl
    all_goals contradiction
  · rcases right with other | (other | (other | (other | (other | (other | other)))))
    all_goals try contradiction
    simp only [label, BaseLabel.connectorLength.injEq] at equal
    have portEqual : length = other := by
      apply TypeACompletionPortCoordinate.Coordinate.ext object profile
      · apply Subtype.ext
        exact equal.1
      · exact equal.2
    subst other
    rfl

end BaseCoordinate

noncomputable def anchored (producer : ReturnProducer object profile)
    (port : Port object profile) :=
  producer.produce object profile port

noncomputable def firstEntry (producer : ReturnProducer object profile)
    (port : Port object profile) :=
  TypeAFirstEntryCoordinate.select object profile port
    (anchored object profile producer port)

noncomputable def connector (producer : ReturnProducer object profile)
    (port : Port object profile) :=
  TypeAReceiverEntryChannel.Connector.extract object profile port
    (anchored object profile producer port)
    (firstEntry object profile producer port)

private noncomputable def listSupport (values : List V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact values.toFinset

private noncomputable def pairSupport (left right : V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {left, right}

private noncomputable def fourSupport (a b c d : V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {a, b, c, d}

/-- The declared support of each base label.  Trace incidence uses the whole
parent trace (not merely the displayed vertex).  Return and connector labels
retain their actual proof-selected paths; first-entry incidence retains the
terminal port and the exact entering edge. -/
noncomputable def declaredSupport (producer : ReturnProducer object profile) :
    BaseCoordinate object profile → Finset V := by
  classical
  exact fun
  | .inl cubic => listSupport object
      ((profile.trace object cubic).support.map (fun vertex => vertex.1))
  | .inr (.inl incidence) => incidence.support object profile
  | .inr (.inr (.inl port)) => pairSupport object
      (port.receiver object profile).1 (port.outside object profile)
  | .inr (.inr (.inr (.inl port))) =>
      listSupport object (anchored object profile producer port).path.support ∪
        pairSupport object (port.receiver object profile).1 (port.outside object profile)
  | .inr (.inr (.inr (.inr (.inl port)))) =>
      let first := firstEntry object profile producer port
      fourSupport object (port.receiver object profile).1 (port.outside object profile)
        (first.entry object profile port (anchored object profile producer port))
        (first.predecessor object profile port (anchored object profile producer port))
  | .inr (.inr (.inr (.inr (.inr (.inl port))))) =>
      listSupport object (connector object profile producer port).path.support ∪
        pairSupport object (port.receiver object profile).1 (port.outside object profile)
  | .inr (.inr (.inr (.inr (.inr (.inr port))))) =>
      listSupport object (connector object profile producer port).path.support ∪
        pairSupport object (port.receiver object profile).1 (port.outside object profile)

theorem canonicalTrace_mem_declaredSupport (producer : ReturnProducer object profile)
    (cubic : Cubic object profile) {vertex : V}
    (member : vertex ∈
      (profile.trace object cubic).support.map (fun value => value.1)) :
    vertex ∈ declaredSupport object profile producer
      (BaseCoordinate.canonicalTrace object profile cubic) := by
  classical
  simpa [BaseCoordinate.canonicalTrace, declaredSupport, listSupport] using member

theorem canonicalReturn_mem_declaredSupport (producer : ReturnProducer object profile)
    (port : Port object profile) {vertex : V}
    (member : vertex ∈ (anchored object profile producer port).path.support) :
    vertex ∈ declaredSupport object profile producer
      (BaseCoordinate.canonicalReturn object profile port) := by
  classical
  simp [BaseCoordinate.canonicalReturn, declaredSupport, listSupport, pairSupport, member]

theorem connectorPath_mem_declaredSupport (producer : ReturnProducer object profile)
    (port : Port object profile) {vertex : V}
    (member : vertex ∈ (connector object profile producer port).path.support) :
    vertex ∈ declaredSupport object profile producer
      (BaseCoordinate.connectorPath object profile port) := by
  classical
  simp [BaseCoordinate.connectorPath, declaredSupport, listSupport, pairSupport, member]

theorem connectorLength_mem_declaredSupport (producer : ReturnProducer object profile)
    (port : Port object profile) {vertex : V}
    (member : vertex ∈ (connector object profile producer port).path.support) :
    vertex ∈ declaredSupport object profile producer
      (BaseCoordinate.connectorLength object profile port) := by
  classical
  simp [BaseCoordinate.connectorLength, declaredSupport, listSupport, pairSupport, member]

/-- Each constructor is a different response-value label.  This prevents an
accidental quotient from identifying two coordinate kinds merely because a
vertex or natural number happens to coincide. -/
inductive BaseValue
  | canonicalTrace (support : List V)
  | traceIncidence (vertex : V) (internalDegree : Nat) (terminal : Bool)
  | completionPort (receiver outside : V)
  | canonicalReturn (support : List V)
  | firstEntryReceiver (entry predecessor : V)
  | connectorPath (support : List V)
  | connectorLength (length : Nat)

noncomputable def value (producer : ReturnProducer object profile) :
    BaseCoordinate object profile → BaseValue (V := V)
  | .inl cubic => .canonicalTrace
      ((profile.trace object cubic).support.map (fun vertex => vertex.1))
  | .inr (.inl incidence) => .traceIncidence
      (incidence.ambientVertex object profile)
      (incidence.internalDegree object profile)
      (incidence.terminal object profile)
  | .inr (.inr (.inl port)) => .completionPort
      (port.receiver object profile).1 (port.outside object profile)
  | .inr (.inr (.inr (.inl port))) => .canonicalReturn
      (anchored object profile producer port).path.support
  | .inr (.inr (.inr (.inr (.inl port)))) =>
      let first := firstEntry object profile producer port
      .firstEntryReceiver
        (first.entry object profile port (anchored object profile producer port))
        (first.predecessor object profile port (anchored object profile producer port))
  | .inr (.inr (.inr (.inr (.inr (.inl port))))) => .connectorPath
      (connector object profile producer port).path.support
  | .inr (.inr (.inr (.inr (.inr (.inr port))))) =>
      let anchored := anchored object profile producer port
      let first := firstEntry object profile producer port
      let connector := connector object profile producer port
      .connectorLength (connector.length object profile port anchored first)

/-- The complete graph-level datum asserted by one locally available D5
coordinate.  Keeping these four fields explicit prevents a fixed-alphabet
normalization from silently discarding the coordinate label or its complete
declared support. -/
structure ExactDatum where
  kind : BaseKind
  label : BaseCoordinate object profile
  support : Finset V
  value : BaseValue (V := V)

noncomputable def exactDatum (producer : ReturnProducer object profile)
    (coordinate : BaseCoordinate object profile) : ExactDatum object profile where
  kind := coordinate.kind object profile
  label := coordinate
  support := declaredSupport object profile producer coordinate
  value := value object profile producer coordinate

theorem exactDatum_injective (producer : ReturnProducer object profile) :
    Function.Injective (exactDatum object profile producer) := by
  intro left right equal
  exact congrArg ExactDatum.label equal

/-! ## Carrier-first execution

The paper's D5 clause is evaluated on the already selected bounded carrier.
The schedules below therefore start from an explicit enumeration of that
carrier.  They do not filter the global support-source or completion-port
schedules. -/

/-- A trace incidence whose complete parent trace lies in the carrier. -/
abbrev LocalTraceIncidence (carrier : Finset V) :=
  {coordinate : TraceIncidence object profile //
    coordinate.support object profile ⊆ carrier}

abbrev CarrierVertex (carrier : Finset V) := {vertex : V // vertex ∈ carrier}

abbrev LocalCubic (carrier : Finset V) :=
  {cubic : Cubic object profile // cubic.1.1 ∈ carrier}

def IsCarrierCubic (carrier : Finset V) (vertex : CarrierVertex carrier) : Prop :=
  ∃ supportMem : vertex.1 ∈ profile.support,
    (profile.supportObject object).degree ⟨vertex.1, supportMem⟩ = 3

noncomputable def isCarrierCubicDecidable (carrier : Finset V)
    (vertex : CarrierVertex carrier) : Decidable (IsCarrierCubic object profile carrier vertex) :=
  Classical.propDecidable _

noncomputable def carrierCubicEquiv (carrier : Finset V) :
    {vertex : CarrierVertex carrier // IsCarrierCubic object profile carrier vertex} ≃
      LocalCubic object profile carrier where
  toFun vertex := by
    let supportMem := Classical.choose vertex.2
    let cubic := Classical.choose_spec vertex.2
    exact ⟨⟨⟨vertex.1.1, supportMem⟩, cubic⟩, vertex.1.2⟩
  invFun cubic :=
    ⟨⟨cubic.1.1.1, cubic.2⟩, ⟨cubic.1.1.2, cubic.1.2⟩⟩
  left_inv := by intro vertex; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro cubic; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl

/-- Cubic sources obtained by validating only the supplied carrier vertices. -/
@[implicit_reducible]
noncomputable def localCubicsFromCarrier (carrier : Finset V)
    (carrierVertices : FinEnum (CarrierVertex carrier)) :
    FinEnum (LocalCubic object profile carrier) := by
  let accepted := Core.Enumeration.subtype carrierVertices
    (IsCarrierCubic object profile carrier)
    (isCarrierCubicDecidable object profile carrier)
  letI : FinEnum {vertex : CarrierVertex carrier //
      IsCarrierCubic object profile carrier vertex} := accepted
  exact FinEnum.ofEquiv _ (carrierCubicEquiv object profile carrier).symm

private noncomputable def traceSupport (cubic : Cubic object profile) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact ((profile.trace object cubic).support.map (fun vertex => vertex.1)).toFinset

abbrev SupportedLocalCubic (carrier : Finset V) :=
  {cubic : LocalCubic object profile carrier //
    traceSupport object profile cubic.1 ⊆ carrier}

@[implicit_reducible]
noncomputable def supportedLocalCubicsFromCarrier (carrier : Finset V)
    (carrierVertices : FinEnum (CarrierVertex carrier)) :
    FinEnum (SupportedLocalCubic object profile carrier) :=
  Core.Enumeration.subtype
    (localCubicsFromCarrier object profile carrier carrierVertices)
    (fun cubic => traceSupport object profile cubic.1 ⊆ carrier)
    (by classical exact fun _ => inferInstance)

abbrev CarrierTracePosition (carrier : Finset V) :=
  Sigma fun cubic : SupportedLocalCubic object profile carrier =>
    Fin ((profile.trace object cubic.1.1).length + 1)

noncomputable def carrierTracePositionEquiv (carrier : Finset V) :
    CarrierTracePosition object profile carrier ≃ LocalTraceIncidence object profile carrier where
  toFun coordinate := ⟨⟨coordinate.1.1.1, coordinate.2⟩, coordinate.1.2⟩
  invFun coordinate := by
    let cubic : LocalCubic object profile carrier :=
      ⟨coordinate.1.1, coordinate.2 (coordinate.1.source_mem_support object profile)⟩
    exact ⟨⟨cubic, coordinate.2⟩, coordinate.1.2⟩
  left_inv := by intro coordinate; cases coordinate; rfl
  right_inv := by intro coordinate; apply Subtype.ext; cases coordinate.1; rfl

/-- Trace positions are generated only after a carrier source has been
validated and its unique canonical trace has been proved wholly supported. -/
@[implicit_reducible]
noncomputable def localTraceIncidencesFromCarrier (carrier : Finset V)
    (carrierVertices : FinEnum (CarrierVertex carrier)) :
    FinEnum (LocalTraceIncidence object profile carrier) := by
  letI : FinEnum (SupportedLocalCubic object profile carrier) :=
    supportedLocalCubicsFromCarrier object profile carrier carrierVertices
  letI : (cubic : SupportedLocalCubic object profile carrier) →
      FinEnum (Fin ((profile.trace object cubic.1.1).length + 1)) := fun _ => inferInstance
  exact FinEnum.ofEquiv (CarrierTracePosition object profile carrier)
    (carrierTracePositionEquiv object profile carrier).symm

abbrev LocalPort (carrier : Finset V) :=
  {port : Port object profile //
    (port.receiver object profile).1 ∈ carrier ∧ port.outside object profile ∈ carrier}

def IsCarrierPort (carrier : Finset V)
    (pair : CarrierVertex carrier × CarrierVertex carrier) : Prop :=
  ∃ supportMem : pair.1.1 ∈ profile.support,
    (profile.supportObject object).degree ⟨pair.1.1, supportMem⟩ ≤ 2 ∧
      object.graph.Adj pair.1.1 pair.2.1 ∧ pair.2.1 ∉ profile.support

noncomputable def isCarrierPortDecidable (carrier : Finset V)
    (pair : CarrierVertex carrier × CarrierVertex carrier) :
    Decidable (IsCarrierPort object profile carrier pair) := Classical.propDecidable _

noncomputable def carrierPortEquiv (carrier : Finset V) :
    {pair : CarrierVertex carrier × CarrierVertex carrier //
      IsCarrierPort object profile carrier pair} ≃ LocalPort object profile carrier where
  toFun pair := by
    let supportMem := Classical.choose pair.2
    let properties := Classical.choose_spec pair.2
    let degree := properties.1
    let adjacent := properties.2.1
    let outside := properties.2.2
    let receiver : TypeACompletionPortCoordinate.Receiver object profile :=
      ⟨⟨pair.1.1.1, supportMem⟩, degree⟩
    let neighbor : TypeACompletionPortCoordinate.Neighbor object profile receiver :=
      ⟨pair.1.2.1, adjacent⟩
    exact ⟨⟨receiver, ⟨neighbor, outside⟩⟩, pair.1.1.2, pair.1.2.2⟩
  invFun port :=
    ⟨(⟨(port.1.receiver object profile).1, port.2.1⟩,
       ⟨port.1.outside object profile, port.2.2⟩),
      ⟨(port.1.receiver object profile).2,
        port.1.receiver_internal_degree_le_two object profile,
        port.1.adjacent object profile,
        port.1.outside_not_mem_support object profile⟩⟩
  left_inv := by
    intro pair
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv := by
    intro port
    apply Subtype.ext
    apply TypeACompletionPortCoordinate.Coordinate.ext object profile <;> rfl

/-- Completion ports reconstructed from carrier endpoint pairs.  Only local
membership, internal degree, one adjacency, and outside-support are tested. -/
@[implicit_reducible]
noncomputable def localPortsFromCarrier (carrier : Finset V)
    (carrierVertices : FinEnum (CarrierVertex carrier)) :
    FinEnum (LocalPort object profile carrier) := by
  letI : FinEnum (CarrierVertex carrier) := carrierVertices
  let pairs : FinEnum (CarrierVertex carrier × CarrierVertex carrier) := inferInstance
  let accepted := Core.Enumeration.subtype pairs
    (IsCarrierPort object profile carrier)
    (isCarrierPortDecidable object profile carrier)
  letI : FinEnum {pair : CarrierVertex carrier × CarrierVertex carrier //
      IsCarrierPort object profile carrier pair} := accepted
  exact FinEnum.ofEquiv _ (carrierPortEquiv object profile carrier).symm

abbrev LocalPortFamily (producer : ReturnProducer object profile)
    (carrier : Finset V) (wrap : Port object profile → BaseCoordinate object profile) :=
  {port : LocalPort object profile carrier //
    declaredSupport object profile producer (wrap port.1) ⊆ carrier}

@[implicit_reducible]
noncomputable def localPortFamilyFromCarrier
    (producer : ReturnProducer object profile) (carrier : Finset V)
    (carrierVertices : FinEnum (CarrierVertex carrier))
    (wrap : Port object profile → BaseCoordinate object profile) :
    FinEnum (LocalPortFamily object profile producer carrier wrap) :=
  Core.Enumeration.subtype
    (localPortsFromCarrier object profile carrier carrierVertices)
    (fun port => declaredSupport object profile producer (wrap port.1) ⊆ carrier)
    (by classical exact fun _ => inferInstance)

/-- The seven paper families, generated from carrier sources and carrier
endpoint pairs before any return/connector support test is made. -/
abbrev CarrierBaseCoordinate (producer : ReturnProducer object profile)
    (carrier : Finset V) :=
  SupportedLocalCubic object profile carrier ⊕
  LocalTraceIncidence object profile carrier ⊕
  LocalPortFamily object profile producer carrier (BaseCoordinate.completionPort object profile) ⊕
  LocalPortFamily object profile producer carrier (BaseCoordinate.canonicalReturn object profile) ⊕
  LocalPortFamily object profile producer carrier (BaseCoordinate.firstEntryReceiver object profile) ⊕
  LocalPortFamily object profile producer carrier (BaseCoordinate.connectorPath object profile) ⊕
  LocalPortFamily object profile producer carrier (BaseCoordinate.connectorLength object profile)

@[implicit_reducible]
noncomputable def carrierBaseCoordinates (producer : ReturnProducer object profile)
    (carrier : Finset V) (carrierVertices : FinEnum (CarrierVertex carrier)) :
    FinEnum (CarrierBaseCoordinate object profile producer carrier) := by
  letI : FinEnum (SupportedLocalCubic object profile carrier) :=
    supportedLocalCubicsFromCarrier object profile carrier carrierVertices
  letI : FinEnum (LocalTraceIncidence object profile carrier) :=
    localTraceIncidencesFromCarrier object profile carrier carrierVertices
  letI : FinEnum (LocalPortFamily object profile producer carrier
      (BaseCoordinate.completionPort object profile)) :=
    localPortFamilyFromCarrier object profile producer carrier carrierVertices _
  letI : FinEnum (LocalPortFamily object profile producer carrier
      (BaseCoordinate.canonicalReturn object profile)) :=
    localPortFamilyFromCarrier object profile producer carrier carrierVertices _
  letI : FinEnum (LocalPortFamily object profile producer carrier
      (BaseCoordinate.firstEntryReceiver object profile)) :=
    localPortFamilyFromCarrier object profile producer carrier carrierVertices _
  letI : FinEnum (LocalPortFamily object profile producer carrier
      (BaseCoordinate.connectorPath object profile)) :=
    localPortFamilyFromCarrier object profile producer carrier carrierVertices _
  letI : FinEnum (LocalPortFamily object profile producer carrier
      (BaseCoordinate.connectorLength object profile)) :=
    localPortFamilyFromCarrier object profile producer carrier carrierVertices _
  exact inferInstance

private theorem port_pair_mem_of_supported
    (producer : ReturnProducer object profile) (carrier : Finset V)
    (port : Port object profile) (coordinate : BaseCoordinate object profile)
    (coordinateIsPort : coordinate = BaseCoordinate.completionPort object profile port ∨
      coordinate = BaseCoordinate.canonicalReturn object profile port ∨
      coordinate = BaseCoordinate.firstEntryReceiver object profile port ∨
      coordinate = BaseCoordinate.connectorPath object profile port ∨
      coordinate = BaseCoordinate.connectorLength object profile port)
    (supported : declaredSupport object profile producer coordinate ⊆ carrier) :
    (port.receiver object profile).1 ∈ carrier ∧ port.outside object profile ∈ carrier := by
  classical
  rcases coordinateIsPort with rfl | rfl | rfl | rfl | rfl
  all_goals constructor <;> apply supported <;>
    simp [BaseCoordinate.completionPort, BaseCoordinate.canonicalReturn,
      BaseCoordinate.firstEntryReceiver, BaseCoordinate.connectorPath,
      BaseCoordinate.connectorLength, declaredSupport, pairSupport, fourSupport]

/-- Public support bridge for the five port-indexed base families. -/
theorem port_endpoints_mem_declaredSupport
    (producer : ReturnProducer object profile) (carrier : Finset V)
    (port : Port object profile) (coordinate : BaseCoordinate object profile)
    (coordinateIsPort : coordinate = BaseCoordinate.completionPort object profile port ∨
      coordinate = BaseCoordinate.canonicalReturn object profile port ∨
      coordinate = BaseCoordinate.firstEntryReceiver object profile port ∨
      coordinate = BaseCoordinate.connectorPath object profile port ∨
      coordinate = BaseCoordinate.connectorLength object profile port)
    (supported : declaredSupport object profile producer coordinate ⊆ carrier) :
    (port.receiver object profile).1 ∈ carrier ∧ port.outside object profile ∈ carrier :=
  port_pair_mem_of_supported object profile producer carrier port coordinate
    coordinateIsPort supported

/-- The exact locally retained base schedule.  It filters only the declared
finite schedule and never enumerates ambient paths, contexts, or graphs. -/
abbrev LocalBaseCoordinate (producer : ReturnProducer object profile)
    (carrier : Finset V) :=
  {coordinate : BaseCoordinate object profile //
    declaredSupport object profile producer coordinate ⊆ carrier}

/-! ## Carrier-role normalization of exact base values -/

/-- The seven D5 value labels with every carrier vertex replaced by a local
role.  Naturals and Boolean observations are retained literally.  Thus this
alphabet contains no ambient vertex identity while still distinguishing all
seven clauses of the paper. -/
inductive RoleValue (R : Type*)
  | canonicalTrace (support : List R)
  | traceIncidence (vertex : R) (internalDegree : Nat) (terminal : Bool)
  | completionPort (receiver outside : R)
  | canonicalReturn (support : List R)
  | firstEntryReceiver (entry predecessor : R)
  | connectorPath (support : List R)
  | connectorLength (length : Nat)

/-- Replace only the vertex payload of an exact D5 value by carrier roles. -/
def BaseValue.toRoleValue {R : Type*} (encode : V → R) :
    BaseValue (V := V) → RoleValue R
  | .canonicalTrace support => .canonicalTrace (support.map encode)
  | .traceIncidence vertex degree terminal =>
      .traceIncidence (encode vertex) degree terminal
  | .completionPort receiver outside =>
      .completionPort (encode receiver) (encode outside)
  | .canonicalReturn support => .canonicalReturn (support.map encode)
  | .firstEntryReceiver entry predecessor =>
      .firstEntryReceiver (encode entry) (encode predecessor)
  | .connectorPath support => .connectorPath (support.map encode)
  | .connectorLength length => .connectorLength length

/-- Decode a role-labelled value back to the ambient vertex type.  This is
used only in the proof that a carrier-role code loses no local D5 datum. -/
def RoleValue.decode {R : Type*} (decode : R → V) :
    RoleValue R → BaseValue (V := V)
  | .canonicalTrace support => .canonicalTrace (support.map decode)
  | .traceIncidence vertex degree terminal =>
      .traceIncidence (decode vertex) degree terminal
  | .completionPort receiver outside =>
      .completionPort (decode receiver) (decode outside)
  | .canonicalReturn support => .canonicalReturn (support.map decode)
  | .firstEntryReceiver entry predecessor =>
      .firstEntryReceiver (decode entry) (decode predecessor)
  | .connectorPath support => .connectorPath (support.map decode)
  | .connectorLength length => .connectorLength length

/-- Exact role-normalized value of one locally supported base coordinate. -/
noncomputable def roleValue {R : Type*} (encode : V → R)
    (producer : ReturnProducer object profile) (carrier : Finset V)
    (coordinate : LocalBaseCoordinate object profile producer carrier) : RoleValue R :=
  (value object profile producer coordinate.1).toRoleValue encode

private theorem map_decode_encode_of_mem {R : Type*}
    (encode : V → R) (decode : R → V) (carrier : Finset V)
    (recovers : ∀ vertex, vertex ∈ carrier → decode (encode vertex) = vertex)
    (values : List V) (supported : ∀ vertex ∈ values, vertex ∈ carrier) :
    (values.map encode).map decode = values := by
  classical
  rw [List.map_map]
  calc
    List.map (decode ∘ encode) values = List.map id values :=
      List.map_congr_left (fun vertex member =>
        recovers vertex (supported vertex member))
    _ = values := List.map_id values

/-- Decoding the carrier-role normalization recovers the exact labelled D5
value.  The hypothesis is local: decoding need only invert roles on the
already supplied carrier. -/
theorem roleValue_decode_exact {R : Type*} (encode : V → R) (decode : R → V)
    (producer : ReturnProducer object profile) (carrier : Finset V)
    (recovers : ∀ vertex, vertex ∈ carrier → decode (encode vertex) = vertex)
    (coordinate : LocalBaseCoordinate object profile producer carrier) :
    (roleValue object profile encode producer carrier coordinate).decode decode =
      value object profile producer coordinate.1 := by
  classical
  rcases coordinate with ⟨coordinate, supported⟩
  rcases coordinate with cubic | (incidence | (port | (returned | (entry | (path | length)))))
  · simp only [roleValue, value, BaseValue.toRoleValue, RoleValue.decode]
    congr 1
    apply map_decode_encode_of_mem encode decode carrier recovers
    intro vertex member
    apply supported
    simpa [declaredSupport, listSupport] using member
  · simp only [roleValue, value, BaseValue.toRoleValue, RoleValue.decode]
    congr 1
    apply recovers
    apply supported
    simpa [declaredSupport] using
      incidence.ambientVertex_mem_support object profile
  · simp only [roleValue, value, BaseValue.toRoleValue, RoleValue.decode]
    congr 1
    · apply recovers
      exact supported (by simp [declaredSupport, pairSupport])
    · apply recovers
      exact supported (by simp [declaredSupport, pairSupport])
  · simp only [roleValue, value, BaseValue.toRoleValue, RoleValue.decode]
    congr 1
    apply map_decode_encode_of_mem encode decode carrier recovers
    intro vertex member
    exact supported (by simp [declaredSupport, listSupport, pairSupport, member])
  · simp only [roleValue, value, BaseValue.toRoleValue, RoleValue.decode]
    congr 1
    · apply recovers
      exact supported (by simp [declaredSupport, fourSupport])
    · apply recovers
      exact supported (by simp [declaredSupport, fourSupport])
  · simp only [roleValue, value, BaseValue.toRoleValue, RoleValue.decode]
    congr 1
    apply map_decode_encode_of_mem encode decode carrier recovers
    intro vertex member
    exact supported (by simp [declaredSupport, listSupport, pairSupport, member])
  · rfl

/-- Equality of role-normalized values reflects equality of the complete
labelled local datum; conversely equal exact data have equal role codes. -/
theorem roleValue_eq_iff {R : Type*} (encode : V → R) (decode : R → V)
    (producer : ReturnProducer object profile) (carrier : Finset V)
    (recovers : ∀ vertex, vertex ∈ carrier → decode (encode vertex) = vertex)
    (left right : LocalBaseCoordinate object profile producer carrier) :
    roleValue object profile encode producer carrier left =
        roleValue object profile encode producer carrier right ↔
      value object profile producer left.1 = value object profile producer right.1 := by
  constructor
  · intro equal
    rw [← roleValue_decode_exact object profile encode decode producer carrier recovers left,
      ← roleValue_decode_exact object profile encode decode producer carrier recovers right]
    exact congrArg (RoleValue.decode decode) equal
  · intro equal
    exact congrArg (BaseValue.toRoleValue encode) equal

noncomputable def carrierBaseEquiv (producer : ReturnProducer object profile)
    (carrier : Finset V) :
    CarrierBaseCoordinate object profile producer carrier ≃
      LocalBaseCoordinate object profile producer carrier where
  toFun coordinate := by
    rcases coordinate with cubic | (incidence | (port | (returned | (entry | (path | length)))))
    · exact ⟨BaseCoordinate.canonicalTrace object profile cubic.1.1, by
        simpa [BaseCoordinate.canonicalTrace, declaredSupport, listSupport,
          traceSupport] using cubic.2⟩
    · exact ⟨BaseCoordinate.traceIncidence object profile incidence.1, incidence.2⟩
    · exact ⟨BaseCoordinate.completionPort object profile port.1.1, port.2⟩
    · exact ⟨BaseCoordinate.canonicalReturn object profile returned.1.1, returned.2⟩
    · exact ⟨BaseCoordinate.firstEntryReceiver object profile entry.1.1, entry.2⟩
    · exact ⟨BaseCoordinate.connectorPath object profile path.1.1, path.2⟩
    · exact ⟨BaseCoordinate.connectorLength object profile length.1.1, length.2⟩
  invFun coordinate := by
    rcases coordinate with ⟨coordinate, supported⟩
    rcases coordinate with cubic | (incidence | (port | (returned | (entry | (path | length)))))
    · have traceSupported : traceSupport object profile cubic ⊆ carrier := by
        simpa [BaseCoordinate.canonicalTrace, declaredSupport, listSupport,
          traceSupport] using supported
      have sourceSupported : cubic.1.1 ∈ carrier := traceSupported (by
        classical
        simp only [traceSupport, List.mem_toFinset, List.mem_map]
        exact ⟨cubic.1, profile.cubic_mem_trace_support object cubic, rfl⟩)
      exact .inl ⟨⟨cubic, sourceSupported⟩, traceSupported⟩
    · exact .inr (.inl ⟨incidence, supported⟩)
    · change declaredSupport object profile producer
          (BaseCoordinate.completionPort object profile port) ⊆ carrier at supported
      exact .inr (.inr (.inl ⟨⟨port,
        port_pair_mem_of_supported object profile producer carrier port
          (BaseCoordinate.completionPort object profile port) (Or.inl rfl) supported⟩,
        supported⟩))
    · change declaredSupport object profile producer
          (BaseCoordinate.canonicalReturn object profile returned) ⊆ carrier at supported
      exact .inr (.inr (.inr (.inl ⟨⟨returned,
        port_pair_mem_of_supported object profile producer carrier returned
          (BaseCoordinate.canonicalReturn object profile returned) (Or.inr (Or.inl rfl)) supported⟩,
        supported⟩)))
    · change declaredSupport object profile producer
          (BaseCoordinate.firstEntryReceiver object profile entry) ⊆ carrier at supported
      exact .inr (.inr (.inr (.inr (.inl ⟨⟨entry,
        port_pair_mem_of_supported object profile producer carrier entry
          (BaseCoordinate.firstEntryReceiver object profile entry)
          (Or.inr (Or.inr (Or.inl rfl))) supported⟩, supported⟩))))
    · change declaredSupport object profile producer
          (BaseCoordinate.connectorPath object profile path) ⊆ carrier at supported
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨⟨path,
        port_pair_mem_of_supported object profile producer carrier path
          (BaseCoordinate.connectorPath object profile path)
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) supported⟩, supported⟩)))))
    · change declaredSupport object profile producer
          (BaseCoordinate.connectorLength object profile length) ⊆ carrier at supported
      exact .inr (.inr (.inr (.inr (.inr (.inr ⟨⟨length,
        port_pair_mem_of_supported object profile producer carrier length
          (BaseCoordinate.connectorLength object profile length)
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) supported⟩, supported⟩)))))
  left_inv := by
    intro coordinate
    rcases coordinate with cubic | (incidence | (port | (returned | (entry | (path | length)))))
    all_goals rfl
  right_inv := by
    rintro ⟨coordinate, supported⟩
    rcases coordinate with cubic | (incidence | (port | (returned | (entry | (path | length)))))
    all_goals apply Subtype.ext <;> rfl

/-- Carrier-first execution of the complete seven-family D5 base signature,
proved equivalent to the paper's declared-support coordinate subtype. -/
@[implicit_reducible]
noncomputable def localBaseCoordinatesFromCarrier
    (producer : ReturnProducer object profile) (carrier : Finset V)
    (carrierVertices : FinEnum (CarrierVertex carrier)) :
    FinEnum (LocalBaseCoordinate object profile producer carrier) := by
  letI : FinEnum (CarrierBaseCoordinate object profile producer carrier) :=
    carrierBaseCoordinates object profile producer carrier carrierVertices
  exact FinEnum.ofEquiv (CarrierBaseCoordinate object profile producer carrier)
    (carrierBaseEquiv object profile producer carrier).symm

theorem localBaseCoordinate_mem_fromCarrier
    (producer : ReturnProducer object profile) (carrier : Finset V)
    (carrierVertices : FinEnum (CarrierVertex carrier))
    (coordinate : LocalBaseCoordinate object profile producer carrier) :
    coordinate ∈ (localBaseCoordinatesFromCarrier object profile producer carrier
      carrierVertices).orderedValues :=
  (localBaseCoordinatesFromCarrier object profile producer carrier carrierVertices).mem_orderedValues _

@[implicit_reducible]
noncomputable def localBaseCoordinates (producer : ReturnProducer object profile)
    (carrier : Finset V) : FinEnum (LocalBaseCoordinate object profile producer carrier) :=
  Core.Enumeration.subtype (baseCoordinates object profile)
    (fun coordinate => declaredSupport object profile producer coordinate ⊆ carrier)
    (by classical exact fun _ => inferInstance)

theorem localBaseCoordinate_mem (producer : ReturnProducer object profile)
    (carrier : Finset V) (coordinate : BaseCoordinate object profile)
    (supported : declaredSupport object profile producer coordinate ⊆ carrier) :
    (⟨coordinate, supported⟩ : LocalBaseCoordinate object profile producer carrier) ∈
      (localBaseCoordinates object profile producer carrier).orderedValues :=
  (localBaseCoordinates object profile producer carrier).mem_orderedValues _

@[implicit_reducible]
noncomputable def localTraceIncidences (carrier : Finset V) :
    FinEnum (LocalTraceIncidence object profile carrier) :=
  Core.Enumeration.subtype
    (TypeATraceIncidenceCoordinate.coordinates object profile)
    (fun coordinate => coordinate.support object profile ⊆ carrier)
    (by classical exact fun _ => inferInstance)

namespace LocalTraceIncidence

noncomputable def sourceInCarrier (carrier : Finset V)
    (coordinate : LocalTraceIncidence object profile carrier) : {v : V // v ∈ carrier} :=
  ⟨coordinate.1.source object profile |>.1.1,
    coordinate.2 (coordinate.1.source_mem_support object profile)⟩

noncomputable def positionInCarrier (carrier : Finset V)
    (coordinate : LocalTraceIncidence object profile carrier) : Fin carrier.card := by
  refine ⟨coordinate.1.position object profile, ?_⟩
  have supportLe : (coordinate.1.support object profile).card ≤ carrier.card :=
    Finset.card_le_card coordinate.2
  rw [coordinate.1.support_card_eq_length_add_one object profile] at supportLe
  exact lt_of_le_of_lt (coordinate.1.position_le_length object profile) (by omega)

noncomputable def embedding (carrier : Finset V) :
    LocalTraceIncidence object profile carrier → {v : V // v ∈ carrier} × Fin carrier.card :=
  fun coordinate =>
    (sourceInCarrier object profile carrier coordinate,
      positionInCarrier object profile carrier coordinate)

theorem embedding_injective (carrier : Finset V) :
    Function.Injective (embedding object profile carrier) := by
  intro left right equal
  obtain ⟨⟨leftSource, leftPosition⟩, leftSupported⟩ := left
  obtain ⟨⟨rightSource, rightPosition⟩, rightSupported⟩ := right
  have sourceEqual : leftSource = rightSource := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [embedding, sourceInCarrier,
      TypeATraceIncidenceCoordinate.Coordinate.source] using
      congrArg (fun output => output.1.1) equal
  subst rightSource
  have positionEqual : leftPosition = rightPosition := by
    apply Fin.ext
    simpa [embedding, positionInCarrier,
      TypeATraceIncidenceCoordinate.Coordinate.position] using
      congrArg (fun output => output.2.1) equal
  subst rightPosition
  apply Subtype.ext
  rfl

end LocalTraceIncidence

/-- Source-by-position accounting on the literal carrier.  This is the bound
used by the paper; it neither scans nor counts vertices outside the carrier. -/
theorem localTraceIncidences_card_le_square (carrier : Finset V) :
    (localTraceIncidences object profile carrier).card ≤ carrier.card * carrier.card := by
  letI : FinEnum {v : V // v ∈ carrier} := Core.Enumeration.subtype
    object.input.vertices (fun vertex => vertex ∈ carrier)
      (by classical exact fun _ => inferInstance)
  letI : FinEnum (LocalTraceIncidence object profile carrier) :=
    localTraceIncidences object profile carrier
  rw [FinEnum.card_eq_fintypeCard]
  calc
    Fintype.card (LocalTraceIncidence object profile carrier) ≤
        Fintype.card ({v : V // v ∈ carrier} × Fin carrier.card) :=
      Fintype.card_le_of_injective (LocalTraceIncidence.embedding object profile carrier)
        (LocalTraceIncidence.embedding_injective object profile carrier)
    _ = carrier.card * carrier.card := by simp

theorem localTraceIncidences_card_le_900 (carrier : Finset V)
    (carrierBound : carrier.card ≤ 30) :
    (localTraceIncidences object profile carrier).card ≤ 900 := by
  calc
    (localTraceIncidences object profile carrier).card ≤ carrier.card * carrier.card :=
      localTraceIncidences_card_le_square object profile carrier
    _ ≤ 30 * 30 := Nat.mul_le_mul carrierBound carrierBound
    _ = 900 := by decide

theorem localTraceIncidencesFromCarrier_card_le_900 (carrier : Finset V)
    (carrierVertices : FinEnum (CarrierVertex carrier))
    (carrierBound : carrier.card ≤ 30) :
    (localTraceIncidencesFromCarrier object profile carrier carrierVertices).card ≤ 900 := by
  letI : FinEnum (CarrierVertex carrier) := carrierVertices
  letI : FinEnum (LocalTraceIncidence object profile carrier) :=
    localTraceIncidencesFromCarrier object profile carrier carrierVertices
  rw [FinEnum.card_eq_fintypeCard]
  calc
    Fintype.card (LocalTraceIncidence object profile carrier) ≤
        Fintype.card (CarrierVertex carrier × Fin carrier.card) :=
      Fintype.card_le_of_injective (LocalTraceIncidence.embedding object profile carrier)
        (LocalTraceIncidence.embedding_injective object profile carrier)
    _ = carrier.card * carrier.card := by simp
    _ ≤ 30 * 30 := Nat.mul_le_mul carrierBound carrierBound
    _ = 900 := by decide

/-- Primitive-decision envelope for the carrier-first schedule: one source
validation scan, at most one carrier-length trace check per source, one local
endpoint-pair scan, and five support filters over those pairs. -/
def carrierVisibleChecks (carrier : Finset V) : Nat :=
  carrier.card + 7 * carrier.card ^ 2

theorem carrierVisibleChecks_le_5516 (carrier : Finset V)
    (carrierBound : carrier.card ≤ 28) :
    carrierVisibleChecks carrier ≤ 5516 := by
  unfold carrierVisibleChecks
  calc
    carrier.card + 7 * carrier.card ^ 2 ≤ 28 + 7 * 28 ^ 2 :=
      Nat.add_le_add carrierBound
        (Nat.mul_le_mul_left 7 (Nat.pow_le_pow_left carrierBound 2))
    _ = 5516 := by decide

/-- D5 families whose declared coordinates arise only after a later named
producer in the manuscript. -/
inductive RoutedKind
  | receiverEntryChannel
  | receiverEntryChannelLabel
  | connectorBandConstraint
  | crossPortThetaConstraint
  | silentBasinResponse
  | carrierRestriction
  | carrierLabelledSubcoordinate

/-- Exact upstream producer required for each routed D5 family. -/
inductive Origin
  | receiverEntryReturn
  | saturatedReceiverClassifier
  | route8SilentBasin
  | route8EssentialCarrierCore

def requiredOrigin : RoutedKind → Origin
  | .receiverEntryChannel => .receiverEntryReturn
  | .receiverEntryChannelLabel => .receiverEntryReturn
  | .connectorBandConstraint => .receiverEntryReturn
  | .crossPortThetaConstraint => .saturatedReceiverClassifier
  | .silentBasinResponse => .route8SilentBasin
  | .carrierRestriction => .route8EssentialCarrierCore
  | .carrierLabelledSubcoordinate => .route8EssentialCarrierCore

/-- A typed residual at the exact producer boundary.  It records only which
family is pending and where the manuscript produces it; it contains no
coordinate, response value, or downstream theorem. -/
structure Pending (producer : ReturnProducer object profile) (carrier : Finset V) where
  kind : RoutedKind
  origin : Origin
  originExact : origin = requiredOrigin kind

def pending (producer : ReturnProducer object profile) (carrier : Finset V)
    (kind : RoutedKind) : Pending object profile producer carrier :=
  ⟨kind, requiredOrigin kind, rfl⟩

theorem pending_origin_exact (producer : ReturnProducer object profile)
    (carrier : Finset V) (kind : RoutedKind) :
    (pending object profile producer carrier kind).origin = requiredOrigin kind := rfl

end StructuralExhaustion.Graph.TypeAFullD5Signature
