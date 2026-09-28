import PoincareConjecture.Definitions.Ch15.SurgeryEndPolicy

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem SurgeryEndCut.disjoint_compact_component
    {g : RiemannianMetric 3 M} {N : EpsilonNeck g}
    (cut : SurgeryEndCut N) {x : M} (hC : IsCompact (connectedComponent x)) :
    Disjoint cut.tail (connectedComponent x) := by
  have hc : IsPreconnected cut.tail := by
    rw [cut.component_eq]
    exact isPreconnected_connectedComponentIn
  refine Set.disjoint_left.2 fun y hy hyC => ?_
  apply cut.escapes_compact (connectedComponent x) hC
  simpa only [← connectedComponent_eq hyC] using hc.subset_connectedComponent hy

theorem SurgeryEventTerminalPolicy.compact_component_retained
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    {E : SurgeryEventData g₀ K P slice metric T} (policy : SurgeryEventTerminalPolicy E)
    {x : E.terminal.carrier} (hC : IsCompact (connectedComponent x))
    (hlow : ∃ y ∈ connectedComponent x,
      E.limit_connection.scalarCurvature y ≤ (P.delta T * P.r T)⁻¹ ^ 2) :
    connectedComponent x ⊆ E.limit_identify.map '' E.retained_pre := by
  rw [policy.retained_eq]
  obtain ⟨z, hz, hR⟩ := hlow
  intro y hy
  refine ⟨⟨z, hR, ?_⟩, ?_⟩
  · simpa only [← connectedComponent_eq hz] using hy
  · intro htail
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 htail
    exact Set.disjoint_left.1 ((policy.cuts i).disjoint_compact_component hC) hi hy

theorem SurgeryEventTerminalPolicy.high_component_discarded
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    {E : SurgeryEventData g₀ K P slice metric T} (policy : SurgeryEventTerminalPolicy E)
    {x : E.terminal.carrier}
    (hhigh : ∀ y ∈ connectedComponent x,
      (P.delta T * P.r T)⁻¹ ^ 2 < E.limit_connection.scalarCurvature y) :
    Disjoint (connectedComponent x) (E.limit_identify.map '' E.retained_pre) := by
  rw [policy.retained_eq]
  refine Set.disjoint_left.2 fun y hy hret => ?_
  obtain ⟨z, hR, hyz⟩ := hret.1
  have heq : connectedComponent z = connectedComponent x :=
    (connectedComponent_eq hyz).trans (connectedComponent_eq hy).symm
  have hz : z ∈ connectedComponent x := heq ▸ mem_connectedComponent
  exact (hhigh z hz).not_ge hR

theorem SurgeryVanishingEventTerminalPolicy.scalar_limit_gt
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    {V : SurgeryVanishingEventData P slice metric T}
    (policy : SurgeryVanishingEventTerminalPolicy V)
    (x : (slice V.tMinus).carrier) {R : ℝ}
    (hlim : Filter.Tendsto (fun t => (V.pre_flow.connection t).scalarCurvature x)
      (nhdsWithin T (Set.Iio T)) (𝓝 R)) :
    (P.delta T * P.r T)⁻¹ ^ 2 < R := by
  obtain ⟨L, hL, s, hs, hR⟩ := policy x
  have heventually : ∀ᶠ t in nhdsWithin T (Set.Iio T),
      L ≤ (V.pre_flow.connection t).scalarCurvature x :=
    Filter.mem_of_superset (Ico_mem_nhdsLT hs.2) fun t ht => (hR t ht).le
  exact hL.trans_le (ge_of_tendsto hlim heventually)

end PoincareConjecture
