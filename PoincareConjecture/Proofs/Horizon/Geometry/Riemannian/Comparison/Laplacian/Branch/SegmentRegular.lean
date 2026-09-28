import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Nonsingular







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem isInvertible_mfderiv_on_minimizing_segment
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {p : M} {R : ℝ}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R)) (he0 : e 0 = p)
    (hinit : (mfderiv (𝓡 n) (𝓡 n) e 0).IsInvertible)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R) (hv0 : v ≠ 0)
    (hmin : g.edist p (e v) = ENNReal.ofReal ‖v‖)
    (hend : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible) :
    ∀ s ∈ Icc (0 : ℝ) 1, (mfderiv (𝓡 n) (𝓡 n) e (s • v)).IsInvertible := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with rfl | hs0
  · rw [zero_smul]
    exact hinit
  rcases eq_or_lt_of_le hs.2 with rfl | hs1
  · rw [one_smul]
    exact hend
  have hR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hnorm : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hs0.le]
  have hqnorm : s⁻¹ * ‖s • v‖ = ‖v‖ := by
    rw [hnorm, ← mul_assoc, inv_mul_cancel₀ hs0.ne', one_mul]
  have hqv : s⁻¹ • (s • v) = v := by
    rw [smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
  apply g.isInvertible_mfderiv_of_minimizing_extension D he he0 hinit hgeo hspeed
    (v := s • v) (q := s⁻¹)
  · rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg v)).trans_lt (by simpa using hR)
  · exact smul_ne_zero hs0.ne' hv0
  · exact (one_lt_inv₀ hs0).mpr hs1
  · simpa only [hqnorm] using hR
  · simpa only [hqnorm, hqv] using hmin

end PoincareConjecture.RiemannianMetric
