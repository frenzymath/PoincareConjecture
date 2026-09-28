import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingGeometry









set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.Proofs.M47



theorem seed_density_of_scaled_density
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (g : RiemannianMetric 3 M) {Q : ℝ} (hQ : 0 < Q) (x : M) (k r : ℝ)
    (hdensity : ENNReal.ofReal (k * (Real.sqrt Q * r) ^ 3) ≤
      calibratedMetricVolume (M13.scaleSmoothMetric g Q hQ)
        (RiemannianMetric.ball (M13.scaleSmoothMetric g Q hQ) x (Real.sqrt Q * r))) :
    ENNReal.ofReal (k * r ^ 3) ≤ calibratedMetricVolume g (g.ball x r) := by
  have hpow : Q ^ (3 / 2 : ℝ) = (Real.sqrt Q) ^ 3 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hQ,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    calc
      Q * Real.sqrt Q = (Real.sqrt Q) ^ 2 * Real.sqrt Q := by rw [Real.sq_sqrt hQ.le]
      _ = _ := by ring
  rw [M13.scaleSmoothMetric_ball, M13.scaleSmoothMetric_volume] at hdensity
  simp only [Real.rpow_eq_pow, Nat.cast_ofNat] at hdensity
  rw [hpow, mul_pow, mul_left_comm k,
    ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg Q) 3)] at hdensity
  exact (ENNReal.mul_le_mul_iff_right
    (a := ENNReal.ofReal ((Real.sqrt Q) ^ 3))
    (ENNReal.ofReal_pos.mpr (pow_pos (Real.sqrt_pos.mpr hQ) 3)).ne'
    ENNReal.ofReal_ne_top).mp hdensity

end PoincareConjecture.Proofs.M47
