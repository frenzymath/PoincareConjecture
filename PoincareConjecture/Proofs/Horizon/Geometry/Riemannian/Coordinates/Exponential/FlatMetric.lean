import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.NearEuclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.FirstJet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.RadialConvexity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

theorem pullbackCoefficients_eq_innerSL_of_flat_radial
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ u w, g.pullbackCoefficients e 0 u w = inner ℝ u w)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    (hflat : ∀ t ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (e (t • v)) = 0)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖) :
    g.pullbackCoefficients e v = innerSL ℝ := by
  have hdiag (w : EuclideanSpace ℝ (Fin n)) :
      g.pullbackCoefficients e v w w = inner ℝ w w := by
    have herr := g.radial_geodesic_metric_error D he hnorm hgeo hv
      (fun t ht => (hflat t ht).le) hspeed w
    have hz : |g.pullbackCoefficients e v w w - ‖w‖ ^ 2| = 0 := by
      apply le_antisymm _ (abs_nonneg _)
      simpa only [zero_mul, zero_div, add_zero] using herr
    rw [real_inner_self_eq_norm_sq]
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  ext u w
  have hs : g.pullbackCoefficients e v w u = g.pullbackCoefficients e v u w :=
    g.symm (e v) _ _
  have hp := hdiag (u + w)
  simp only [map_add, add_apply, inner_add_left, inner_add_right,
    hdiag, hs, real_inner_comm w u] at hp
  rw [real_inner_comm u w] at hp
  change g.pullbackCoefficients e v u w = inner ℝ u w
  linarith

theorem euclideanCoefficients_eq_innerSL_of_flat_gauss
    {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (D : LeviCivitaData g) {R : ℝ}
    (hgauss : ∀ x w : EuclideanSpace ℝ (Fin n), g.inner x x w = inner ℝ x w)
    (hflat : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      D.curvatureTensorNorm x = 0) :
    ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      g.euclideanCoefficients x = innerSL ℝ := by
  have hzero : g.euclideanCoefficients 0 = innerSL ℝ :=
    CoordinateExponential.metric_zero_eq_innerSL_of_gauss
      ((g.contDiffAt_euclideanCoefficients 0).differentiableAt (by simp))
      (Eventually.of_forall hgauss)
  have hnorm (u w : EuclideanSpace ℝ (Fin n)) : g.inner 0 u w = inner ℝ u w :=
    congrArg (fun B => B u w) hzero
  have hid : g.pullbackCoefficients id = g.euclideanCoefficients := by
    ext x u w
    simp only [pullbackCoefficients, mfderiv_id, euclideanCoefficients]
    rfl
  intro x hx
  rw [← hid]
  apply g.pullbackCoefficients_eq_innerSL_of_flat_radial D contMDiffOn_id
    (by rw [hid, hzero]; exact fun _ _ => rfl)
    (fun v _ t _ => isGeodesicOn_ray_of_gauss hgauss v t (mem_univ t)) hx
  · intro t ht
    change D.curvatureTensorNorm (t • x) = 0
    apply hflat
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)).trans_lt
      (by simpa only [Metric.mem_ball, dist_zero_right, one_mul] using hx)
  · intro t ht
    rw [mfderiv_eq_fderiv]
    change g.tangentNorm (t • x)
      (fderiv ℝ (fun s : ℝ => s • x) t (1 : ℝ)) = ‖x‖
    rw [fderiv_eq_smul_deriv, one_smul]
    have hd : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const x
    rw [hd.deriv]
    have hnormt : g.inner (t • x) x x = inner ℝ x x := by
      change g.euclideanCoefficients (t • x) x x = inner ℝ x x
      by_cases ht0 : t = 0
      · rw [ht0, zero_smul, hzero]
        rfl
      · have hg := hgauss (t • x) x
        change g.euclideanCoefficients (t • x) (t • x) x = inner ℝ (t • x) x at hg
        simp only [map_smul, smul_apply, smul_eq_mul, real_inner_smul_left] at hg
        exact (mul_left_cancel₀ ht0) hg
    change Real.sqrt (g.inner (t • x) x x) = ‖x‖
    rw [hnormt, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg x)]

end PoincareConjecture.RiemannianMetric
