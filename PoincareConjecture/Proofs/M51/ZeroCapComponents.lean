import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M51.OpenVolume

set_option autoImplicit false

open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

theorem retainedPre_isClopen_of_zero_caps
    (E : SurgeryEventData g₀ K P slice metric T) (hzero : E.cap_count = 0) :
    IsClopen E.retained_pre := by
  apply isClopen_iff_frontier_eq_empty.mpr
  rw [E.pre_boundary]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
  exact Nat.not_lt_zero i.val (hzero ▸ i.isLt)

theorem discardedComponent_of_zero_caps
    (E : SurgeryEventData g₀ K P slice metric T)
    (hzero : E.cap_count = 0) (hproper : E.retained_pre ≠ Set.univ) :
    ∃ x : (slice E.tMinus).carrier,
      connectedComponent x ⊆ E.retained_preᶜ ∧
      0 < calibratedMetricVolume (E.pre_flow.metric E.tMinus) (connectedComponent x) := by
  obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr hproper
  exact ⟨x, (E.retainedPre_isClopen_of_zero_caps hzero).compl.connectedComponent_subset hx,
    M51.calibratedMetricVolume_component_pos _ x⟩

end PoincareConjecture.SurgeryEventData
