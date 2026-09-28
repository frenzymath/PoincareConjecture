import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.VolumeDeficit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.FlatVolume

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem m23LocalCurvatureEstimate_of_predecessors
    {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
    (P : M23NormalizedKappaCompactnessPredecessors) :
    M23LocalCurvatureEstimate S := by
  by_contra hn
  obtain ⟨C, g, D, p, hc, hflat, hvolume, hdeficit⟩ :=
    S.exists_complete_flat_slice_with_volume_deficit P hn
  simp only [calibratedMetricVolume_eq_volumeMeasure] at hvolume hdeficit
  have hunit := g.volumeMeasure_ball_eq_euclidean_of_flat_of_volume_lower_bound
    D hc hflat p S.kappa_pos hvolume 1 (by norm_num)
  rw [one_pow, mul_one] at hunit
  rw [hunit] at hdeficit
  have hω := RiemannianMetric.euclideanUnitBallVolume_pos 3
  have hle := (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ (3 / 4 : ℝ) * RiemannianMetric.euclideanUnitBallVolume 3)).mp hdeficit
  linarith

end PoincareConjecture
