import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactCohomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.IntegralCochains

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe u

namespace Poincare.Topology

theorem integralCompactSupportCohomology_one_isZero
    (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [SimplyConnectedSpace X] :
    IsZero (integralCompactSupportCohomology X 1) := by
  let e := integralCompactSupportCohomologyIso (X := X) 1
  have hz : IsZero (integralCohomology X 1) := integral_cohomology_one_isZero X
  exact hz.of_iso e

end Poincare.Topology
