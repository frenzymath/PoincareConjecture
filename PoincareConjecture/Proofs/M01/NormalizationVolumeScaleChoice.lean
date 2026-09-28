import PoincareConjecture.Proofs.M01.NormalizationVolumeScaling










set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

theorem m01_rescaledMetric_smallBall_lower_bound
    (g : RiemannianMetric 3 M) (r₀ : ℝ) (_hr₀ : 0 < r₀)
    (hball : ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 ≤
        normalizedMetricVolume g (g.ball x r))
    (c : ℝ) (hc : 0 < c)
    (hscale : 1 ≤ Real.sqrt c * r₀) :
    ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 ≤
        normalizedMetricVolume (m01RescaledMetric g c hc)
          ((m01RescaledMetric g c hc).ball x r) := by
  intro x r hr hr1
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsmall : 0 < r / Real.sqrt c := div_pos hr hsqrt
  have hsmall_le : r / Real.sqrt c ≤ r₀ := by
    apply (div_le_iff₀ hsqrt).mpr
    calc
      r ≤ 1 := hr1
      _ ≤ Real.sqrt c * r₀ := hscale
      _ = r₀ * Real.sqrt c := by ring
  have hbase := hball x (r / Real.sqrt c) hsmall hsmall_le
  rw [m01RescaledMetric_ball g c hc x r,
    m01RescaledMetric_normalizedMetricVolume g c hc]
  have hfactor : ENNReal.ofReal (Real.sqrt c) ^ 3 *
      ((euclideanUnitBallLebesgueVolume / 2) *
        ENNReal.ofReal (r / Real.sqrt c) ^ 3) =
      (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 := by
    rw [ENNReal.ofReal_div_of_pos hsqrt]
    simp only [div_eq_mul_inv, mul_pow]
    rw [← ENNReal.inv_pow]
    calc
      ENNReal.ofReal (Real.sqrt c) ^ 3 *
          (euclideanUnitBallLebesgueVolume / 2 *
            (ENNReal.ofReal r ^ 3 * (ENNReal.ofReal (Real.sqrt c) ^ 3)⁻¹)) =
          (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 *
            (ENNReal.ofReal (Real.sqrt c) ^ 3 *
              (ENNReal.ofReal (Real.sqrt c) ^ 3)⁻¹) := by ac_rfl
      _ = (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 := by
        rw [ENNReal.mul_inv_cancel]
        · simp
        · exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr hsqrt).ne'
        · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  calc
    (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 =
        ENNReal.ofReal (Real.sqrt c) ^ 3 *
          ((euclideanUnitBallLebesgueVolume / 2) *
            ENNReal.ofReal (r / Real.sqrt c) ^ 3) := hfactor.symm
    _ ≤ ENNReal.ofReal (Real.sqrt c) ^ 3 *
          normalizedMetricVolume g (g.ball x (r / Real.sqrt c)) := by
      gcongr

end PoincareConjecture
