import PoincareConjecture.Proofs.M02.Topology.IntegralCompactCohomology
import PoincareConjecture.Proofs.M02.Topology.IntegralCochains

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem integralCompactSupportCohomology_one_isZero
    (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [SimplyConnectedSpace X] :
    IsZero (integralCompactSupportCohomology X 1) := by
  let e := integralCompactSupportCohomologyIso (X := X) 1
  have hz : IsZero (integralCohomology X 1) := integral_cohomology_one_isZero X
  exact hz.of_iso e

end PoincareConjecture.Proofs.M02.Topology
