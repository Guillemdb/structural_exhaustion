import Hypostructure.CT7.Automation
import Hypostructure.Graph.Response

/-!
# Graph specialization of CT7

Graph contributes only exact same-boundary gluing and target evaluation.  The
representative pair and context-coordinate schedule remain predecessor-ledger
queries, while Core owns both scans and every route.
-/

namespace Hypostructure.Graph.CT7

universe uPrevious u uContext uCoordinate

/-- Interpret CT7 realization and exact response as a target on a graph formed
by gluing one same-boundary piece to an outside context. -/
noncomputable abbrev targetSpec
    (Previous : Type uPrevious)
    {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context) :
    _root_.Hypostructure.CT7.Spec Previous where
  Representative := BoundaryPiece boundary
  system := Graph.Response.targetSystem Target decideTarget Context outside
    Coordinate decode
  Realizes := fun _previous piece context =>
    Target (Graph.glue piece (outside context))

/-- Build the complete CT7 capability when the residual-owned graph contexts
literally cover the semantic context type. -/
noncomputable def targetCapabilityOfExactContexts
    {Previous : Type uPrevious}
    {boundary : Boundary.{u}}
    {Target : FiniteObject.{u} -> Prop}
    (decideTarget : forall object, Decidable (Target object))
    {Context : Type uContext}
    {outside : Context -> OutsideContext boundary}
    {Coordinate : Type uCoordinate}
    {decode : Coordinate -> Context}
    (representatives : Core.Residual.Query Previous fun _previous =>
      Core.Response.Representatives (BoundaryPiece boundary))
    (contexts : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration Coordinate)
    (complete : (previous : Previous) -> (context : Context) ->
      Exists fun index : Fin (contexts.read previous).card =>
        context = decode ((contexts.read previous).get index)) :
    _root_.Hypostructure.CT7.Capability
      (targetSpec Previous Target decideTarget Context outside Coordinate
        decode) :=
  _root_.Hypostructure.CT7.Capability.ofExactContexts representatives contexts
    (by
      change DecidableEq Bool
      infer_instance)
    (fun previous coordinate =>
      decideTarget (Graph.glue (representatives.read previous).source
        (outside (decode coordinate))))
    complete

section TerminalSemantics

variable {Previous : Type uPrevious}
  {boundary : Boundary.{u}}
  {Target : FiniteObject.{u} -> Prop}
  {decideTarget : forall object, Decidable (Target object)}
  {Context : Type uContext}
  {outside : Context -> OutsideContext boundary}
  {Coordinate : Type uCoordinate}
  {decode : Coordinate -> Context}

local notation "graphSpec" =>
  targetSpec Previous Target decideTarget Context outside Coordinate decode

/-- A graph CT7 realization certificate is a genuine glued-target witness. -/
theorem realization_target
    {capability : _root_.Hypostructure.CT7.Capability graphSpec}
    {previous : Previous}
    (certificate : _root_.Hypostructure.CT7.RealizationCertificate capability
      previous) :
    Target (Graph.glue (capability.representativesAt previous).source
      (outside certificate.context)) :=
  certificate.realizes

/-- A graph CT7 neutral certificate transports the target through every
outside context. -/
theorem neutrality_target_iff
    {capability : _root_.Hypostructure.CT7.Capability graphSpec}
    {previous : Previous}
    (certificate : _root_.Hypostructure.CT7.NeutralityCertificate capability
      previous)
    (context : Context) :
    Target (Graph.glue (capability.representativesAt previous).source
        (outside context)) ↔
      Target (Graph.glue (capability.representativesAt previous).replacement
        (outside context)) := by
  simpa [targetSpec] using certificate.target_iff
    (Graph.Response.targetSemantics Target decideTarget Context outside
      Coordinate decode) context

end TerminalSemantics

end Hypostructure.Graph.CT7
