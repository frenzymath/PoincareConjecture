import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Neck.NeckBoundaryVolume
import PoincareLib.Geometry.RicciFlow.Surgery.Volume.LossData

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/RetainedBoundaryVolume.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Zero volume of the retained boundary on both sides

Morgan-Tian Lemma 17.12, p. 410, and Theorem 15.9, pp. 363-366.
The literal pre-frontier is a finite union of inverse central spheres.
Their images under the actual limit and retention maps are null.
Only within-set smoothness is used on the closed retained region.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareMT.SurgeryVolume

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

/-- The actual retained pre-frontier has null terminal image
(MT Lemma 17.12, p. 410; M49 derivation 25). -/
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

/-- The actual retained pre-frontier has null post-surgery image
(MT Lemma 17.12, p. 410; M49 derivation 25). -/
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

end PoincareMT.SurgeryVolume
