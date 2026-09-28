import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CenterSelection
open Set Filter Topology Poincare.CurvatureIntegral
open scoped Manifold ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.RiemannianMetric
theorem exists_near_min_badAscentRadius_subset_centers_of_tendsto_zero
    {n : ℕ} {M : ℕ → Type*} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, RiemannianMetric n (M j))
    (hc : ∀ j, MetricComplete (g j))
    (E : ∀ j, Set (M j)) (hE : ∀ j, IsCompact (E j))
    {c b ρ : ℝ} (hc1 : c < 1) (hb : 0 < b) (hρ : 0 < ρ)
    (p : ∀ j, M j) (hp : ∀ j, p j ∈ E j)
    (href : Tendsto (fun j => letI := (g j).toMetricSpace;
      badAscentRadius c b (p j)) atTop (𝓝 0)) :
    ∃ q : ∀ j, M j,
      (∀ j, letI := (g j).toMetricSpace
        q j ∈ E j ∧ dist (p j) (q j) ≤ ρ ∧
        badAscentRadius c b (q j) ≤ badAscentRadius c b (p j) ∧
        ∀ z ∈ E j, dist (p j) z ≤ ρ →
          badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z) ∧
      Tendsto (fun j => letI := (g j).toMetricSpace;
        badAscentRadius c b (q j)) atTop (𝓝 0) := by
  classical
  let (j : ℕ) : MetricSpace (M j) := (g j).toMetricSpace
  have hselect (j : ℕ) : ∃ q : M j, q ∈ E j ∧
      dist (p j) q ≤ ρ ∧ badAscentRadius c b q ≤ badAscentRadius c b (p j) ∧
      ∀ z ∈ E j, dist (p j) z ≤ ρ →
        badAscentRadius c b q ≤ 2 * badAscentRadius c b z := by
    have hcompact : IsCompact (E j ∩ Metric.closedBall (p j) ρ) :=
      (hE j).inter_right Metric.isClosed_closedBall
    obtain ⟨q, hq, hqref, hqmin⟩ :=
      (g j).exists_near_min_badAscentRadius_on_isCompact (hc j) hc1 hb hcompact
        ⟨hp j, Metric.mem_closedBall_self hρ.le⟩
    refine ⟨q, hq.1, ?_, hqref, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_comm] using hq.2
    · intro z hz hzρ
      exact hqmin z ⟨hz, by simpa only [Metric.mem_closedBall, dist_comm] using hzρ⟩
  choose q hqE hqball hqref hqmin using hselect
  exact ⟨q, fun j => ⟨hqE j, hqball j, hqref j, hqmin j⟩,
    squeeze_zero (fun j => badAscentRadius_nonneg c b (q j)) hqref href⟩
end PoincareConjecture.RiemannianMetric
