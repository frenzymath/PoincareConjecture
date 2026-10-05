import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.ReturnedLoop

/-!
# Convex functions on returning exponential rays

Opposite terminal velocities turn an exponential collision into a returning
geodesic. A geodesically convex function at its midpoint is bounded by its
value at the centre. This is the convex-set step of
Maeder--Baumdicker--Seidel, Lemma 5.1, pp. 35--36.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem convex_value_le_center_of_opposite_radial_velocities
    (g : RiemannianMetric n M) (f : M → ℝ)
    (hconvex : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) → ConvexOn ℝ (Icc a b) (f ∘ curve))
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    {v w : EuclideanSpace ℝ (Fin n)} (hv : 2 * ‖v‖ < R) (hw : ‖w‖ < R)
    (hgv : g.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hgw : g.IsGeodesicOn (fun t : ℝ => e (t • w))
      {t : ℝ | t • w ∈ Metric.ball 0 R})
    (heq : e v = e w)
    (hvel : mfderiv (𝓡 n) (𝓡 n) e v v = -mfderiv (𝓡 n) (𝓡 n) e w w) :
    f (e v) ≤ f (e 0) := by
  have hreturn := g.exponential_double_eq_zero_of_opposite_radial_velocities
    he hv hw hgv hgw heq hvel
  have hγ : g.IsGeodesicOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 2) := by
    intro t ht
    apply hgv
    simp only [mem_ofPred_eq, Metric.mem_ball, dist_zero_right,
      norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt hv
  have h := (hconvex _ 0 2 hγ).2
    (show (0 : ℝ) ∈ Icc 0 2 by norm_num)
    (show (2 : ℝ) ∈ Icc 0 2 by norm_num)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [Function.comp_def, hreturn] at h
  linarith

end PoincareMT.RiemannianMetric
