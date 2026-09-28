import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Exhaustion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric

theorem exists_minimizing_geodesic_with_convex_descent
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    (f : M → ℝ)
    (hconvex : ∀ (curve : ℝ → M) (a b : ℝ), g.IsGeodesicOn curve (Icc a b) →
      ConvexOn ℝ (Icc a b) (f ∘ curve))
    {p x : M} (hgap : f p < f x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ curve : ℝ → M,
      g.IsGeodesicOn curve (Ioo (-ε) (1 + ε)) ∧ curve 0 = x ∧ curve 1 = p ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (curve s) (curve t) = ENNReal.ofReal |s - t| * g.edist x p) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, f (curve t) ≤ f x - c * t) ∧
      MapsTo curve (Icc (0 : ℝ) 1) {y | f y ≤ f x} := by
  obtain ⟨ε, hε, curve, hcurve, h0, h1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hcomplete x p
  have hclosed : g.IsGeodesicOn curve (Icc (0 : ℝ) 1) := by
    intro t ht
    exact hcurve t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hconv := hconvex curve 0 1 hclosed
  have hdescent : ∀ t ∈ Icc (0 : ℝ) 1, f (curve t) ≤ f x - (f x - f p) * t := by
    intro t ht
    have h := hconv.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      (sub_nonneg.mpr ht.2) ht.1 (show 1 - t + t = 1 by ring)
    simp only [Function.comp_apply, smul_eq_mul, mul_zero, mul_one, zero_add, h0, h1] at h
    nlinarith
  refine ⟨ε, hε, f x - f p, sub_pos.mpr hgap, curve, hcurve, h0, h1, hmin, hdescent, ?_⟩
  intro t ht
  exact (hdescent t ht).trans (sub_le_self _ (mul_nonneg (sub_nonneg.mpr hgap.le) ht.1))

end PoincareConjecture.RiemannianMetric
