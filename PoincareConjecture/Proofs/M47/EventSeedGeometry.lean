import PoincareConjecture.Proofs.M47.EventSeedEmbedding
import PoincareConjecture.Proofs.M47.RetainedNeckScalar
import PoincareConjecture.Proofs.M47.RetainedNeckVolume
import PoincareConjecture.Proofs.M47.ComponentEstimateCapExclusion










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}



theorem event_retained_center_scalar
    (E : SurgeryEventData g0 K P slice metric T) (D : LeviCivitaData (metric T))
    (i : Fin E.cap_count) :
    D.scalarCurvature (E.local_embed i ((E.local_result i).collapse (E.necks i).neck.center)) =
      (E.necks i).neck.scale⁻¹ ^ 2 := by
  rw [← PoincareConjecture.M47.localResult_scalar_eq E D i]
  exact retained_neck_center_scalar (E.local_result i)



theorem event_retained_center_ball_volume
    (E : SurgeryEventData g0 K P slice metric T) (i : Fin E.cap_count)
    {s : ℝ} (hs : 0 < s) (hscale : s ≤ (E.necks i).neck.scale) :
    ENNReal.ofReal ((M46.canonicalSphereVolumeFloor / 512) * s ^ 3) ≤
      calibratedMetricVolume (metric T)
        ((metric T).ball
          (E.local_embed i ((E.local_result i).collapse (E.necks i).neck.center)) s) := by
  let R := E.local_result i
  let c := R.collapse (E.necks i).neck.center
  have hcont : Continuous (fun y => R.metric.edist c y) :=
    (M36.metric_edist_continuous R.metric).comp (continuous_const.prodMk continuous_id)
  have hmeas : MeasurableSet (R.metric.ball c s) :=
    (isOpen_Iio.preimage hcont).measurableSet
  have hsub : E.local_embed i '' R.metric.ball c s ⊆
      (metric T).ball (E.local_embed i c) s := by
    rintro _ ⟨y, hy, rfl⟩
    exact (local_result_embedding_edist_le E i c y).trans_lt hy
  exact (retained_neck_ball_volume R hs hscale).trans
    ((local_result_embedding_volume_eq E i hmeas).symm.le.trans
      (measure_mono hsub))



theorem event_retained_center_mem_cap
    (E : SurgeryEventData g0 K P slice metric T) (i : Fin E.cap_count) :
    E.local_embed i ((E.local_result i).collapse (E.necks i).neck.center) ∈
      (E.caps i).carrier := by
  rw [← E.local_cap_image i]
  refine mem_image_of_mem _ (frontier_subset_closure ?_)
  rw [← (E.local_result i).cap_boundary]
  exact mem_image_of_mem _ (E.necks i).neck.center_on_central_sphere



theorem event_cap_contact_distance
    (E : SurgeryEventData g0 K P slice metric T) (i : Fin E.cap_count)
    {z : (slice T).carrier} (hz : z ∈ (E.caps i).carrier) :
    (metric T).edist z
      (E.local_embed i ((E.local_result i).collapse (E.necks i).neck.center)) ≤
        ENNReal.ofReal (2 * (E.necks i).neck.scale * (g0.cylindrical_end.radius + 5)) := by
  let c := E.local_embed i ((E.local_result i).collapse (E.necks i).neck.center)
  have hzc := (E.caps i).outer_ball hz
  have hcc := (E.caps i).outer_ball (event_retained_center_mem_cap E i)
  change (metric T).edist (E.caps i).tip z ≤ _ at hzc
  change (metric T).edist (E.caps i).tip c ≤ _ at hcc
  have hscaleEq : ENNReal.ofReal (P.h T * (g0.cylindrical_end.radius + 5)) =
      ENNReal.ofReal ((E.necks i).neck.scale * (g0.cylindrical_end.radius + 5)) := by
    rw [E.neck_scale i]
  have hR : 0 ≤ (E.necks i).neck.scale * (g0.cylindrical_end.radius + 5) :=
    mul_nonneg (E.necks i).neck.scale_pos.le (by linarith [g0.cylindrical_end.radius_pos])
  calc
    _ ≤ (metric T).edist z (E.caps i).tip + (metric T).edist (E.caps i).tip c :=
      M36.metric_edist_triangle (metric T) z (E.caps i).tip c
    _ ≤ ENNReal.ofReal ((E.necks i).neck.scale * (g0.cylindrical_end.radius + 5)) +
        ENNReal.ofReal ((E.necks i).neck.scale * (g0.cylindrical_end.radius + 5)) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (slice T).carrier → Type _) :=
        ⟨(metric T).toRiemannianMetric⟩
      let : PseudoEMetricSpace (slice T).carrier :=
        PseudoEMetricSpace.ofRiemannianMetric (𝓡 3) (slice T).carrier
      change edist z (E.caps i).tip + edist (E.caps i).tip c ≤ _
      rw [edist_comm z (E.caps i).tip]
      exact add_le_add (hzc.trans_eq hscaleEq) (hcc.trans_eq hscaleEq)
    _ = _ := by
      rw [← ENNReal.ofReal_add hR hR]
      congr 1
      ring

end PoincareConjecture.Proofs.M47
