import Hypostructure.PDE.FastTrack.Signature
import Hypostructure.PDE.FastTrack.DirectedExhaustiveness
import Hypostructure.PDE.FastTrack.DefectRouting
import Hypostructure.PDE.FastTrack.DefectRoutingAlignment
import Hypostructure.PDE.FastTrack.TargetCompactification
import Hypostructure.PDE.FastTrack.CapacityProfile
import Hypostructure.PDE.FastTrack.ExactResponseCoverage
import Hypostructure.PDE.FastTrack.ProfileFamily
import Hypostructure.PDE.FastTrack.BoundaryRepair
import Hypostructure.PDE.FastTrack.ConservativeCarrier
import Hypostructure.PDE.FastTrack.EllipticConstraintTail
import Hypostructure.PDE.FastTrack.FluxRadius
import Hypostructure.PDE.FastTrack.Saturation
import Hypostructure.PDE.FastTrack.WindowSchedule
import Hypostructure.PDE.FastTrack.Pipeline

/-!
# PDE fast-track facade

One import exposes the complete PDE fast-track vocabulary.  The row modules
remain separate so each row can specialize a Core strategy or CT, while this
facade gives applications a stable entry point for composing them.
-/
