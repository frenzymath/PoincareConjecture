import PoincareConjecture.Proofs.M15.Thm1_34_LocalVolume
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Noncollapse

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

theorem euclidean_modelVolume_le_modelVolume
    {n : ℕ} (hn : 1 ≤ n) {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) :
    euclideanUnitBallVolume n * r ^ n ≤ modelVolume n K r := by
  have hprofile (t : ℝ) (ht : 0 ≤ t) : t ≤ modelS K t := by
    by_cases hzero : K = 0
    · simp only [hzero, modelS_zero_curvature, le_refl]
    · have hroot : 0 < Real.sqrt K := Real.sqrt_pos.mpr (lt_of_le_of_ne hK (Ne.symm hzero))
      rw [modelS, if_neg hzero, le_div_iff₀ hroot]
      simpa only [mul_comm] using
        Real.self_le_sinh_iff.mpr (mul_nonneg hroot.le ht)
  rw [← modelVolume_zero_curvature hn r]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_nonneg n))
  exact intervalIntegral.integral_mono_on hr
    (intervalIntegrable_modelS_pow n 0 0 r) (intervalIntegrable_modelS_pow n K 0 r)
    (fun t ht => by
      simpa only [modelS_zero_curvature] using
        pow_le_pow_left₀ ht.1 (hprofile t ht.1) (n - 1))

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.Proofs.M15

theorem calibrated_small_ball_lower_bound_of_unit_volume
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {K omega r : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K) (homega : 0 < omega)
    (hcurv : ∀ q, D.curvatureTensorNorm q ≤ K)
    (hvolume : ENNReal.ofReal omega ≤ calibratedMetricVolume g (g.ball p 1))
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (((RiemannianMetric.euclideanUnitBallVolume n /
      RiemannianMetric.modelVolume n K 1) * omega) * r ^ n) ≤
        calibratedMetricVolume g (g.ball p r) := by
  rw [calibratedMetricVolume_eq_volumeMeasure] at hvolume ⊢
  have hbound := (g.smallerBall_volume_lower_bound_of_curvatureTensorNorm_le D p
    hn hK (by norm_num : (0 : ℝ) < 1) homega isClosed_closure.isCompact
    (fun q _ => hcurv q) hvolume hr hr1).2
  apply le_trans (ENNReal.ofReal_le_ofReal _) hbound
  have hmodel := RiemannianMetric.euclidean_modelVolume_le_modelVolume hn hK hr.le
  have hden := RiemannianMetric.modelVolume_pos hn hK (by norm_num : (0 : ℝ) < 1)
  calc
    _ = (RiemannianMetric.euclideanUnitBallVolume n * r ^ n /
        RiemannianMetric.modelVolume n K 1) * omega := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmodel hden.le) homega.le

end PoincareConjecture.Proofs.M15
