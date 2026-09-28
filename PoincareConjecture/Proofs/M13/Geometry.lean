import PoincareConjecture.Proofs.M13.CompatibleTheory
import PoincareConjecture.Definitions.M13SpacetimeRescaling








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

noncomputable def spacetimeRescalingCore
    (hc : CompatibleSpacetimeTheory.{u, u}
      (parabolicSpacetime R.spacetime Q hQ a) R.timeIntervals)
    (hcc : CompatibleSpacetimeTheory.{u, 0}
      (parabolicSpacetime R.spacetime Q hQ a) R.timeIntervals) :
    ParabolicSpacetimeRescaling R Q hQ a where
  atlasRescaling := atlasRescaling A Q hQ a
  realization := rescaledCarrierCore hc hcc
  intervalSystem_eq := rfl
  intervalTransport := parabolicIntervalTransport R.timeIntervals Q hQ a
  chartedSpace_eq := rfl
  identification := parabolicSpacetimeIdentification R.spacetime Q hQ a
  identification_eq := parabolicSpacetimeIdentification_eq R.spacetime Q hQ a
  differential_eq := parabolicSpacetimeIdentification_derivative R.spacetime Q hQ a
  time_differential := parabolicClock_derivative R.spacetime Q a
  timeVector_eq := parabolicSpacetime_timeVector R.spacetime Q hQ a
  horizontal := parabolicSpacetimeHorizontal R.spacetime Q hQ a
  horizontal_val := parabolicSpacetimeHorizontal_val R.spacetime Q hQ a
  horizontal_smooth := parabolicSpacetimeHorizontal_smooth R.spacetime Q hQ a
  horizontal_inverse_smooth := parabolicSpacetimeHorizontal_inverse_smooth R.spacetime Q hQ a
  projection_eq := parabolicSpacetime_projection R.spacetime Q hQ a
  metric_eq := parabolicSpacetime_metric R.spacetime Q hQ a
  sliceIdentification := parabolicSliceIdentification R.spacetime R.slices Q hQ a
  sliceIdentification_eq := parabolicSliceIdentification_val R.spacetime R.slices Q hQ a
  slice_tangent := parabolicSliceIdentification_tangent R.spacetime R.slices Q hQ a
  slice_metric := parabolicSliceIdentification_metric R.spacetime R.slices Q hQ a

noncomputable def spacetimeRescaling (R : GeneralizedFlowCarrierConclusion A)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) : ParabolicSpacetimeRescaling R Q hQ a :=
  spacetimeRescalingCore
    (rescaledCompatibleTheory R.compatible)
    (rescaledCompatibleTheory R.coordinate_compatible)

end PoincareConjecture.M13
