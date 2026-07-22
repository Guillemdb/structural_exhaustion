import Mathlib.Combinatorics.SimpleGraph.Copy
import Hypostructure.Graph.CT1

/-!
# Graph obstructions

The graph layer exposes induced-copy obstructions as a parameterized semantic
target.  Applications supply only the forbidden pattern; CT1 owns the focused
branching, residual extension, trace, and work accounting.
-/

namespace Hypostructure.Graph

universe uPrevious uPattern uVertex

/-- A graph contains the induced obstruction `pattern`. -/
def HasInducedObstruction {PatternVertex : Type uPattern}
    (pattern : SimpleGraph PatternVertex)
    (object : FiniteObject.{uVertex}) : Prop :=
  SimpleGraph.IsIndContained pattern object.graph

/-- A graph is free of the induced obstruction `pattern`. -/
def InducedObstructionFree {PatternVertex : Type uPattern}
    (pattern : SimpleGraph PatternVertex)
    (object : FiniteObject.{uVertex}) : Prop :=
  Not (HasInducedObstruction pattern object)

namespace CT1

/-- Focused proof-carrying CT1 encoding for an arbitrary induced obstruction in
a graph read from the active residual. -/
def focusedInducedObstructionEncoding {Previous : Type uPrevious}
    {PatternVertex : Type uPattern}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (pattern : SimpleGraph PatternVertex) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Encoding profile
      (fun previous active =>
        HasInducedObstruction pattern (object.read previous active)) where
  Code := fun previous active =>
    pattern ↪g (object.read previous active).graph
  Accepts := fun _previous _active _certificate => True
  encode := by
    intro previous active target
    rcases target with ⟨certificate⟩
    exact ⟨certificate, trivial⟩
  decode := by
    intro previous active certificate _accepted
    exact ⟨certificate⟩
  acceptsDecidable := fun _previous _active _certificate => .isTrue trivial

/-- Counted focused CT1 execution for an induced-obstruction certificate
target. -/
noncomputable def executeFocusedInducedObstructionCounted
    {Previous : Type uPrevious} {PatternVertex : Type uPattern}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (pattern : SimpleGraph PatternVertex) (previous : Previous) :
    Core.Counted
      (_root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
        (focusedInducedObstructionEncoding profile object pattern)) :=
  (focusedInducedObstructionEncoding profile object pattern).runCounted previous

/-- Public focused CT1 stage for an induced-obstruction certificate target. -/
noncomputable def executeFocusedInducedObstruction
    {Previous : Type uPrevious} {PatternVertex : Type uPattern}
    (profile : Core.Residual.Focus.Profile Previous)
    (object : Core.Residual.Focus.ActiveQuery profile fun _previous _active =>
      FiniteObject.{uVertex})
    (pattern : SimpleGraph PatternVertex) (previous : Previous) :
    _root_.Hypostructure.CT1.FocusedCertificateEncoding.Stage
      (focusedInducedObstructionEncoding profile object pattern) :=
  (executeFocusedInducedObstructionCounted profile object pattern previous).value

end CT1

end Hypostructure.Graph
