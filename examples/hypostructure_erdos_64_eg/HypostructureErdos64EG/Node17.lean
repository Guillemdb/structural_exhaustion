import Hypostructure.Core.Metadata
import Hypostructure.Graph.InducedPathMaximalPacking
import HypostructureErdos64EG.Node16

namespace HypostructureErdos64EG

open Hypostructure

universe u v

set_option maxHeartbeats 5000000 in
def node17ObjectQuery :
    Core.Residual.Focus.ActiveQuery Node16Focus.{u, v}
      (fun _stage _active => Graph.FiniteObject.{u}) :=
  (node15ObjectQuery.preserve
      (Output := CT1.FocusedCertificateEncoding.Output node15Encoding)).preserve
    (Output := CT1.FocusedCertificateEncoding.C1Evidence node15Encoding)

abbrev Node17Window (stage : Node16Stage.{u, v})
    (active : Node16Focus.Active stage) :=
  Hypostructure.Graph.InducedPathMaximalPacking.Window
    (node17ObjectQuery.read stage active) 13

structure Node17Output (stage : Node16Stage.{u, v})
    (active : Node16Focus.Active stage) where
  selected : Finset (Node17Window stage active)
  selected_mem : selected ∈ Hypostructure.Graph.InducedPathMaximalPacking.admissibleWindowSets
    (node17ObjectQuery.read stage active) 13
  selected_maximal : Maximal
    (fun windows => windows ∈
      Hypostructure.Graph.InducedPathMaximalPacking.admissibleWindowSets
        (node17ObjectQuery.read stage active) 13) selected
  saturated : ∀ window : Node17Window stage active,
    ∃ chosen ∈ selected,
      ¬ Disjoint
        (Hypostructure.Graph.InducedPathMaximalPacking.support
          (node17ObjectQuery.read stage active) 13 window)
        (Hypostructure.Graph.InducedPathMaximalPacking.support
          (node17ObjectQuery.read stage active) 13 chosen) ∨
      window = chosen

set_option maxHeartbeats 1000000 in
abbrev Node17Profile := node15Encoding.{u, v}.C1Profile

set_option maxHeartbeats 1000000 in
abbrev Node17Stage :=
  Core.Residual.Focus.Stage Node17Profile
    (fun (stage : Node16Stage.{u, v})
      (active : Node17Profile.{u, v}.Active stage) =>
      Node17Output stage active)

set_option maxHeartbeats 1000000 in
noncomputable def node17 (previous : Node16Stage.{u, v}) : Node17Stage :=
  (Core.Residual.Focus.runCounted Node17Profile previous
    (fun (active : Node17Profile.{u, v}.Active previous) _checks _exact => {
      selected := Hypostructure.Graph.InducedPathMaximalPacking.maximalWindowSet
        (node17ObjectQuery.read previous active) 13
      selected_mem := Hypostructure.Graph.InducedPathMaximalPacking.maximalWindowSet_mem
        (node17ObjectQuery.read previous active) 13
      selected_maximal := Hypostructure.Graph.InducedPathMaximalPacking.maximalWindowSet_maximal
        (node17ObjectQuery.read previous active) 13
      saturated := Hypostructure.Graph.InducedPathMaximalPacking.maximalWindowSet_saturated
        (node17ObjectQuery.read previous active) 13 })).value

end HypostructureErdos64EG
