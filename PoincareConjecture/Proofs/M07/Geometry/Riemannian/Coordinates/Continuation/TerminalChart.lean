import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.Cauchy









set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric


theorem exists_terminal_compact_chart_of_tendsto
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {a b : ℝ} (hab : a < b) {γ : ℝ → M} {p : M}
    (hγ : Tendsto γ (𝓝[<] b) (𝓝 p)) :
    ∃ t₁ ∈ Ioo a b, ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact K ∧ K ⊆ (extChartAt (𝓡 n) p).target ∧
      ∀ t ∈ Ioo t₁ b, γ t ∈ (extChartAt (𝓡 n) p).source ∧
        extChartAt (𝓡 n) p (γ t) ∈ K := by
  have hU : (extChartAt (𝓡 n) p).target ∈
      𝓝 (extChartAt (𝓡 n) p p) := by
    simpa using extChartAt_target_mem_nhdsWithin (I := 𝓡 n) p
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  let K := Metric.closedBall (extChartAt (𝓡 n) p p) (r / 2)
  have hKU : K ⊆ (extChartAt (𝓡 n) p).target := by
    intro x hx
    apply hrU
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hx (by linarith))
  have hKnhds : (extChartAt (𝓡 n) p) ⁻¹' K ∈ 𝓝 p :=
    (continuousAt_extChartAt p).preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ (half_pos hr))
  have htail : {t | γ t ∈ (extChartAt (𝓡 n) p).source ∧
      extChartAt (𝓡 n) p (γ t) ∈ K} ∈ 𝓝[<] b :=
    hγ (inter_mem (extChartAt_source_mem_nhds p) hKnhds)
  obtain ⟨l, hl, hlγ⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp htail
  obtain ⟨t₁, hat, htb⟩ := exists_between (max_lt hab hl)
  refine ⟨t₁, ⟨lt_of_le_of_lt (le_max_left _ _) hat, htb⟩,
    K, isCompact_closedBall _ _, hKU, ?_⟩
  intro t ht
  exact hlγ ⟨lt_trans (lt_of_le_of_lt (le_max_right _ _) hat) ht.1, ht.2⟩


theorem exists_left_limit_of_compact_edist_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M]
    (g : RiemannianMetric n M) {a b : ℝ} (hab : a < b)
    {γ : ℝ → M} {S : Set M} (hS : IsCompact S)
    (hγS : MapsTo γ (Ioo a b) S) (C : ℝ≥0)
    (hC : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b,
      g.edist (γ s) (γ t) ≤ C * EDist.edist s t) :
    ∃ p ∈ S, Tendsto γ (𝓝[<] b) (𝓝 p) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hI : Ioo a b ∈ 𝓝[<] b :=
    (mem_nhdsLT_iff_exists_Ioo_subset' hab).2 ⟨a, hab, Subset.rfl⟩
  have hL : LipschitzOnWith C γ (Ioo a b) := hC
  have hc : Cauchy (map γ (𝓝[<] b)) :=
    (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le
      hL.uniformContinuousOn (le_principal_iff.mpr hI)
  exact hS.isComplete _ hc (le_principal_iff.mpr (by
    change ∀ᶠ t in 𝓝[<] b, γ t ∈ S
    filter_upwards [hI] with t ht
    exact hγS ht))



theorem exists_terminal_compact_chart_of_edist_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M]
    (g : RiemannianMetric n M) {a b : ℝ} (hab : a < b)
    {γ : ℝ → M} {S : Set M} (hS : IsCompact S)
    (hγS : MapsTo γ (Ioo a b) S) (C : ℝ≥0)
    (hC : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b,
      g.edist (γ s) (γ t) ≤ C * EDist.edist s t) :
    ∃ p ∈ S, ∃ t₁ ∈ Ioo a b, ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact K ∧ K ⊆ (extChartAt (𝓡 n) p).target ∧
      ∀ t ∈ Ioo t₁ b, γ t ∈ (extChartAt (𝓡 n) p).source ∧
        extChartAt (𝓡 n) p (γ t) ∈ K := by
  obtain ⟨p, hpS, hp⟩ := exists_left_limit_of_compact_edist_bound g hab hS hγS C hC
  exact ⟨p, hpS, exists_terminal_compact_chart_of_tendsto hab hp⟩

end PoincareConjecture.RiemannianMetric
