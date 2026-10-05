import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Open.OpenVolume

/-!
# Components removed by a zero-cap event

Once maximality has shown that the retained pre-region is proper, the
zero-cap boundary formula makes that region clopen. Its complement contains
an entire component of positive volume for the actual pre-flow metric.
This is the component-count alternative in Morgan--Tian Lemma 17.12,
printed pp. 410-411; properness remains a separate analytic obligation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

/-- With no inserted caps the retained region has no boundary. -/
theorem retainedPre_isClopen_of_zero_caps
    (E : SurgeryEventData g₀ K P slice metric T) (hzero : E.cap_count = 0) :
    IsClopen E.retained_pre := by
  apply isClopen_iff_frontier_eq_empty.mpr
  rw [E.pre_boundary]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
  exact Nat.not_lt_zero i.val (hzero ▸ i.isLt)

/-- A proper zero-cap retained region omits a whole positive-volume component. -/
theorem discardedComponent_of_zero_caps
    (E : SurgeryEventData g₀ K P slice metric T)
    (hzero : E.cap_count = 0) (hproper : E.retained_pre ≠ Set.univ) :
    ∃ x : (slice E.tMinus).carrier,
      connectedComponent x ⊆ E.retained_preᶜ ∧
      0 < calibratedMetricVolume (E.pre_flow.metric E.tMinus) (connectedComponent x) := by
  obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr hproper
  exact ⟨x, (E.retainedPre_isClopen_of_zero_caps hzero).compl.connectedComponent_subset hx,
    M51.calibratedMetricVolume_component_pos _ x⟩

end PoincareMT.SurgeryEventData
