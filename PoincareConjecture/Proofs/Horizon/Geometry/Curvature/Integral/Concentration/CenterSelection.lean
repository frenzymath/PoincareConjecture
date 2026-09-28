import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RadiusSelection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.CurvatureIntegral
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.RiemannianMetric

theorem exists_near_min_badAscentRadius_centers_of_tendsto_zero
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j))
    {c b ρ : ℝ} (hc1 : c < 1) (hb : 0 < b) (hρ : 0 < ρ)
    (p : ∀ j, M j)
    (href : Tendsto (fun j => letI := (g j).toMetricSpace; badAscentRadius c b (p j))
      atTop (𝓝 0)) :
    ∃ q : ∀ j, M j,
      (∀ j, letI := (g j).toMetricSpace
        dist (p j) (q j) ≤ ρ ∧
        badAscentRadius c b (q j) ≤ badAscentRadius c b (p j) ∧
        ∀ z : M j, dist (p j) z ≤ ρ →
          badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z) ∧
      Tendsto (fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j))
        atTop (𝓝 0) := by
  classical
  let (j : ℕ) : MetricSpace (M j) := (g j).toMetricSpace
  have hselect (j : ℕ) : ∃ q : M j,
      dist (p j) q ≤ ρ ∧ badAscentRadius c b q ≤ badAscentRadius c b (p j) ∧
      ∀ z : M j, dist (p j) z ≤ ρ →
        badAscentRadius c b q ≤ 2 * badAscentRadius c b z := by
    have hcompact : IsCompact (Metric.closedBall (p j) ρ) := by
      rw [(g j).toMetricSpace_closedBall (p j) hρ.le]
      exact (g j).isCompact_closedBall_of_metricComplete (hc j) (p j) ρ
    obtain ⟨q, hq, hqref, hqmin⟩ :=
      (g j).exists_near_min_badAscentRadius_on_isCompact (hc j) hc1 hb hcompact
        (Metric.mem_closedBall_self hρ.le)
    refine ⟨q, ?_, hqref, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_comm] using hq
    · intro z hz
      exact hqmin z (by simpa only [Metric.mem_closedBall, dist_comm] using hz)
  choose q hqball hqref hqmin using hselect
  refine ⟨q, fun j => ⟨hqball j, hqref j, hqmin j⟩, ?_⟩
  exact squeeze_zero (fun j => badAscentRadius_nonneg c b (q j)) hqref href

end PoincareConjecture.RiemannianMetric

namespace Poincare.CurvatureIntegral

theorem eventually_mem_closedBall_of_tendsto_dist_zero
    {X : ℕ → Type*} [∀ j, MetricSpace (X j)]
    (p q z : ∀ j, X j) {ρ : ℝ} (hρ : 0 < ρ)
    (hpq : Tendsto (fun j => dist (p j) (q j)) atTop (𝓝 0))
    (hqz : Tendsto (fun j => dist (q j) (z j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, z j ∈ Metric.closedBall (p j) ρ := by
  have hsum : Tendsto (fun j => dist (p j) (q j) + dist (q j) (z j))
      atTop (𝓝 0) := by simpa only [add_zero] using hpq.add hqz
  filter_upwards [hsum.eventually_lt_const hρ] with j hj
  rw [Metric.mem_closedBall, dist_comm]
  exact ((dist_triangle (p j) (q j) (z j)).trans_lt hj).le

theorem exists_bad_points_of_near_min_badAscentRadius
    {X : ℕ → Type*} [∀ j, MetricSpace (X j)]
    (c b : ℝ) (q z : ∀ j, X j)
    (hpos : ∀ᶠ j in atTop, 0 < badAscentRadius c b (q j))
    (hnear : ∀ᶠ j in atTop,
      badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b (z j))
    (hzero : Tendsto (fun j => badAscentRadius c b (z j)) atTop (𝓝 0)) :
    ∃ y : ∀ j, X j,
      (∀ j, dist (z j) (y j) ≤ badAscentRadius c b (z j)) ∧
      (∀ᶠ j in atTop,
        badAscentRadius c b (q j) / 4 < dist (z j) (y j) ∧
        dist (z j) (y j) ≤ b ∧ ¬ HasLocalDistanceAscent c (z j) (y j)) ∧
      Tendsto (fun j => dist (z j) (y j)) atTop (𝓝 0) := by
  classical
  have hw (j : ℕ) : ∃ y : X j, dist (z j) y ≤ badAscentRadius c b (z j) ∧
      (0 < badAscentRadius c b (q j) ∧
          badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b (z j) →
        badAscentRadius c b (q j) / 4 < dist (z j) y ∧
          dist (z j) y ≤ b ∧ ¬ HasLocalDistanceAscent c (z j) y) := by
    by_cases hj : 0 < badAscentRadius c b (q j) ∧
        badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b (z j)
    · obtain ⟨y, hylo, hyhi, hyb, hybad⟩ :=
        exists_bad_point_of_lt_badAscentRadius
          (show 0 ≤ badAscentRadius c b (q j) / 4 from
            div_nonneg (badAscentRadius_nonneg c b (q j)) (by norm_num))
          (show badAscentRadius c b (q j) / 4 < badAscentRadius c b (z j) by
            linarith only [hj.1, hj.2])
      exact ⟨y, hyhi, fun _ => ⟨hylo, hyb, hybad⟩⟩
    · exact ⟨z j, by simpa only [dist_self] using badAscentRadius_nonneg c b (z j),
        fun h => False.elim (hj h)⟩
  choose y hybound hy using hw
  refine ⟨y, hybound, ?_, squeeze_zero (fun _ => dist_nonneg) hybound hzero⟩
  filter_upwards [hpos, hnear] with j hjpos hjnear
  exact hy j ⟨hjpos, hjnear⟩

end Poincare.CurvatureIntegral
