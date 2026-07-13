import StructuralExhaustion.CT10.Capability

namespace StructuralExhaustion.CT10

universe uAmbient uBranch uDatum uClass uPromotion
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P)
variable (input : Input capability)

structure DirectResidual where
  cls : capability.Class
  direct : capability.Direct cls

structure DirectAbsent : Prop where
  absent : ∀ cls : capability.Class, ¬ capability.Direct cls

structure MissingDatum where
  cls : capability.Class
  empty : row capability input cls = []

structure PromotedResidual where
  directAbsent : DirectAbsent capability
  missing : MissingDatum capability input
  promotion : capability.Promotion
  exact : promotion = capability.promote missing.cls

structure ExhaustiveCertificate : Prop where
  directAbsent : DirectAbsent capability
  populated : ∀ cls : capability.Class,
    ∃ datum : capability.Datum, datum ∈ row capability input cls

end StructuralExhaustion.CT10
