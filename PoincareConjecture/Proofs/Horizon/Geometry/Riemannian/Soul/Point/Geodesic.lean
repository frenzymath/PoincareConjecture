import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.Exponential










noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem globalExponential_eq_center_iff_of_totallyConvex_singleton
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ ({p} : Set M) → curve b ∈ ({p} : Set M) →
      MapsTo curve (Icc a b) ({p} : Set M))
    (v : EuclideanSpace ℝ (Fin n)) :
    g.globalExponential hc p v = p ↔ v = 0 := by
  constructor
  · intro hv
    obtain ⟨N, hcenter, _⟩ :=
      g.exists_zero_containedNormalDisk (S := {p}) (mem_singleton p)
    let t : ℝ := min 1 (N.radius / (2 * (‖v‖ + 1)))
    have hden : 0 < 2 * (‖v‖ + 1) := by positivity
    have ht : 0 < t := lt_min zero_lt_one (div_pos N.radius_pos hden)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htr : t * (2 * (‖v‖ + 1)) ≤ N.radius :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    have hsmall : t • v ∈ Metric.ball 0 N.radius := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le]
      nlinarith [norm_nonneg v]
    have hreturn : g.globalExponential hc p (t • v) = p :=
      mem_singleton_iff.mp (g.globalExponential_smul_mem_of_every_geodesic hc hconv
        (mem_singleton p) (mem_singleton_iff.mpr hv) ⟨ht.le, ht1⟩)
    have hsource : t • v ∈ N.chart.source := N.source_eq.symm ▸ hsmall
    have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ N.chart.source :=
      N.source_eq.symm ▸ Metric.mem_ball_self N.radius_pos
    have hscaled : t • v = 0 := N.chart.injOn hsource hzero (by
      rw [N.chart_eq_globalExponential hc hsource, N.map_zero, hcenter, hreturn])
    exact (smul_eq_zero.mp hscaled).resolve_left ht.ne'
  · rintro rfl
    exact g.globalExponential_zero hc p

end PoincareConjecture.RiemannianMetric
