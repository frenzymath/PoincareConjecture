import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient.LevelDistance

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology

theorem PoincareConjecture.RiemannianMetric.value_gap_le_of_mem_closedBall_common_level
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (hc : PoincareConjecture.MetricComplete g)
    {ι : Type*} (f : ι → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (p x : M) {q R : ℝ} (hq : 0 ≤ q)
    (hlevel : ∀ i, f i x = f i p)
    (hroom : (g.edist p x).toReal + q ≤ R)
    (hgrad : ∀ i z, g.edist p z ≤ ENNReal.ofReal R →
      g.tangentNorm z (g.gradient (f i) z) ≤ 1) :
    ∀ y, g.edist x y ≤ ENNReal.ofReal q → ∀ i, |f i y - f i p| ≤ q := by
  let := g.toMetricSpace
  intro y hy i
  have hxy : dist x y ≤ q := by
    change (g.edist x y).toReal ≤ q
    simpa only [ENNReal.toReal_ofReal hq] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
  have hb := g.abs_sub_le_mul_toReal_edist_of_gradient_bound_closedBall
    hc (hf i) x y (L := 1) (by
      intro z hz
      apply hgrad i z
      have hxz : dist x z ≤ (g.edist x y).toReal := by
        simpa only [Metric.mem_closedBall, dist_comm z x] using hz
      change (g.edist x y).toReal ≤ q at hxy
      have hpz : dist p z ≤ R := (dist_triangle p x z).trans
        (by change dist p x + dist x z ≤ R; change dist p x + q ≤ R at hroom
            linarith)
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top p z)]
      exact ENNReal.ofReal_le_ofReal hpz)
  simp only [NNReal.coe_one, one_mul, hlevel i] at hb
  exact hb.trans hxy
