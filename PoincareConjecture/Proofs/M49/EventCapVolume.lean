import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M49.LocalCapVolume
import PoincareConjecture.Proofs.M49.LocalIsometryVolume










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M49



theorem event_cap_volume_eq_local
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T) (i : Fin E.cap_count) :
    calibratedMetricVolume (metric T) (E.caps i).carrier =
      calibratedMetricVolume (E.local_result i).metric
        (closure ((E.local_result i).cap_map ''
          g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))) := by
  rw [← E.local_cap_image i]
  exact calibratedMetricVolume_image_eq_of_injective_isometry
    (E.local_result i).metric (metric T) (E.local_embed_smooth i)
    (E.local_embed_injective i) (E.local_metric i) isClosed_closure.measurableSet



theorem exists_uniform_event_cap_volume_bound (g₀ : StandardInitialMetric) :
    ∃ Ccap : ℝ, 0 < Ccap ∧ ∀ K : MetricSurgeryConstants,
      ∃ d : ℝ, 0 < d ∧ d ≤ K.delta₀ ∧
        ∀ (P : SurgeryParameters) (slice : ℝ → GeneralizedSliceCarrier.{u})
          (metric : ∀ t, RiemannianMetric 3 (slice t).carrier) (T : ℝ)
          (E : SurgeryEventData g₀ K P slice metric T),
          P.delta T ≤ d → ∀ i : Fin E.cap_count,
            calibratedMetricVolume (metric T) (E.caps i).carrier ≤
              ENNReal.ofReal (Ccap * (P.h T) ^ 3) := by
  obtain ⟨Ccap, hCcap, hK⟩ := exists_uniform_local_cap_volume_bound.{u} g₀
  refine ⟨Ccap, hCcap, ?_⟩
  intro K
  obtain ⟨d, hd, hdK, hbound⟩ := hK K
  refine ⟨d, hd, hdK, ?_⟩
  intro P slice metric T E hdelta i
  have h := hbound E.terminal E.limit_metric (E.necks i) (E.local_result i)
    (by simpa only [E.neck_delta i] using hdelta)
  rw [event_cap_volume_eq_local E i]
  simpa only [E.neck_scale i] using h

end PoincareConjecture.M49
