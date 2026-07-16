import StructuralExhaustion.Core.ConditionalFibreProductCost

/-!
# Deprecated graph compatibility import

The conditional-fibre calculation is entirely finite and is owned by `Core`.
This file preserves the original graph namespace for downstream clients while
they migrate to the Core API; it contains no graph-owned implementation.
-/

namespace StructuralExhaustion.Graph.ConditionalFibreProductCost

universe u v

abbrev Profile := Core.ConditionalFibreProductCost.Profile

namespace Profile

abbrev Ledger (profile : Profile.{u, v}) :=
  Core.ConditionalFibreProductCost.Profile.Ledger profile

abbrev Certificate (profile : Profile.{u, v}) :=
  Core.ConditionalFibreProductCost.Profile.Certificate profile

namespace Certificate

theorem power_le_flat_mul_skeleton (profile : Profile.{u, v})
    (certificate : Certificate profile) :
    profile.safe ^ profile.coordinates.values.length ≤
      profile.flat ^ profile.coordinates.values.length *
        profile.skeletonCount :=
  Core.ConditionalFibreProductCost.Profile.Certificate.power_le_flat_mul_skeleton
    profile certificate

end Certificate

end Profile

end StructuralExhaustion.Graph.ConditionalFibreProductCost
