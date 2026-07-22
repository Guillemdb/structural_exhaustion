import Hypostructure.Graph.InducedPathCold
import Hypostructure.Core.Residual.Query

/-!
# Residual-query ergonomics for cold induced-path data

These constructors are the public node-facing surface.  They derive every
window, incidence, and branch-excess schedule from typed predecessor queries;
the node never accepts a graph copy, a manually selected window, or a detached
ledger payload.
-/

namespace Hypostructure.Graph.InducedPathCold.QuerySurface

open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.Core.Finite
open Hypostructure.Graph.InducedPathMaximalPacking

universe uPrevious u

variable {Previous : Sort uPrevious}

abbrev ObjectQuery :=
  Query Previous (fun _previous => FiniteObject.{u})

noncomputable def selectedWindowsQuery {order : Nat}
    (object : ObjectQuery)
    (packing : Query Previous
      (fun previous => Profile (object.read previous) order)) :
    Query Previous (fun previous =>
      Enumeration (Window (object.read previous) order)) :=
  packing.map fun previous profile => by
    letI : DecidableEq (Window (object.read previous) order) :=
      Classical.decEq _
    exact Enumeration.ofNodupList profile.selected profile.selected_nodup

noncomputable def tokenScheduleQuery {order : Nat}
    (object : ObjectQuery)
    (window : Query Previous (fun previous =>
      Window (object.read previous) order)) :
    Query Previous (fun previous =>
      Enumeration (Token (object.read previous) order (window.read previous))) :=
  window.dependentMap fun _previous activeWindow => tokenSchedule activeWindow

noncomputable def branchExcessQuery {order : Nat}
    (object : ObjectQuery)
    (window : Query Previous (fun previous =>
      Window (object.read previous) order))
    (transit : Query Previous (fun _previous => Nat)) :
    Query Previous (fun previous =>
      List (Token (object.read previous) order (window.read previous))) :=
  window.dependentMap fun previous activeWindow =>
    branchExcess activeWindow (transit.read previous)

noncomputable def branchExcessChecksQuery {order : Nat}
    (object : ObjectQuery)
    (window : Query Previous (fun previous =>
      Window (object.read previous) order)) :
    Query Previous (fun _previous => Nat) :=
  window.map fun _previous activeWindow =>
    branchExcessChecks activeWindow

noncomputable def regularityDecisionQuery {order baseline : Nat}
    (object : ObjectQuery)
    (window : Query Previous (fun previous =>
      Window (object.read previous) order)) :
    Query Previous (fun previous =>
      Decidable (Regularity (object.read previous) order baseline
        (window.read previous))) :=
  window.dependentMap fun _previous activeWindow =>
    regularityDecidable (baseline := baseline) activeWindow

end Hypostructure.Graph.InducedPathCold.QuerySurface
