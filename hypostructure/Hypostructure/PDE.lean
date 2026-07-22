import Hypostructure.PDE.Atlas
import Hypostructure.PDE.Equation
import Hypostructure.PDE.Model
import Hypostructure.PDE.Representation
import Hypostructure.PDE.Observable
import Hypostructure.PDE.Target
import Hypostructure.PDE.Minimality
import Hypostructure.PDE.TargetClosure
import Hypostructure.PDE.Coordinate
import Hypostructure.PDE.LocalTail
import Hypostructure.PDE.FastTrack.Signature
import Hypostructure.PDE.GeneratorForm
import Hypostructure.PDE.Quotient
import Hypostructure.PDE.DirectResistance
import Hypostructure.PDE.StructuralGradient
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
import Hypostructure.PDE.Budget
import Hypostructure.PDE.Contract
import Hypostructure.PDE.CT3
import Hypostructure.PDE.CT1
import Hypostructure.PDE.CT2
import Hypostructure.PDE.CT4
import Hypostructure.PDE.CT5
import Hypostructure.PDE.CT6
import Hypostructure.PDE.CT7
import Hypostructure.PDE.CT8
import Hypostructure.PDE.CT9
import Hypostructure.PDE.CT10
import Hypostructure.PDE.CT11
import Hypostructure.PDE.CT12
import Hypostructure.PDE.CT13
import Hypostructure.PDE.CT14
import Hypostructure.PDE.CT15
import Hypostructure.PDE.CT16
import Hypostructure.PDE.CT17
import Hypostructure.PDE.Strategy

/-!
# Generic PDE specialization

This barrel intentionally excludes `Hypostructure.PDE.NavierStokes`.  A
domain-independent PDE consumer does not acquire model-specific equations or
constants by importing the specialization API.
-/
