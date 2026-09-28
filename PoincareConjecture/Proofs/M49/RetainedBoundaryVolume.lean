import PoincareConjecture.Proofs.M49.NeckBoundaryVolume
import PoincareConjecture.Definitions.M49VolumeLoss

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M49

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

theorem event_terminal_boundary_volume_eq_zero
    (E : SurgeryEventData g₀ K P slice metric T) :
    calibratedMetricVolume E.limit_metric
      (E.limit_identify.map '' frontier E.retained_pre) = 0 := by
  rw [E.pre_boundary, image_iUnion]
  apply measure_iUnion_null
  intro i
  have hnull : calibratedMetricVolume E.limit_metric (E.necks i).neck.central_sphere = 0 := by
    simpa only [image_id] using calibratedMetricVolume_image_central_sphere_eq_zero
      E.limit_metric (E.necks i).neck (f := id) mdifferentiableOn_id
  apply measure_mono_null _ hnull
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  simpa only [E.limit_identify.right_inverse (mem_univ z)] using hz

theorem event_post_boundary_volume_eq_zero
    (E : SurgeryEventData g₀ K P slice metric T) :
    calibratedMetricVolume (metric T)
      (E.retention.map '' frontier E.retained_pre) = 0 := by
  have hclosed := E.retained_pre_compact.isClosed
  rw [E.pre_boundary, image_iUnion]
  apply measure_iUnion_null
  intro i
  rw [image_image]
  apply calibratedMetricVolume_image_central_sphere_eq_zero (metric T) (E.necks i).neck
  apply (E.retention.map_smooth.mdifferentiableOn (by simp)).comp
    ((E.limit_identify.inverse_smooth.mdifferentiableOn (by simp)).mono (subset_univ _))
  intro x hx
  apply hclosed.frontier_subset
  rw [E.pre_boundary]
  exact mem_iUnion.mpr ⟨i, x, hx, rfl⟩

end PoincareConjecture.M49
