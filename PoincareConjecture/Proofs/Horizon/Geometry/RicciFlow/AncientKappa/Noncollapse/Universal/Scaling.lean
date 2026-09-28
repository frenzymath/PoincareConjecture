import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Ordinary
import Mathlib.Analysis.SpecialFunctions.Pow.Real










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]


theorem MetricHomothetyCalculus.ball_volume_lower_bound_iff
    {g : RiemannianMetric n M} {h : RiemannianMetric n N}
    {f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞} {Q : ℝ}
    (H : MetricHomothetyCalculus g h f Q) (hQ : 0 < Q)
    (p : M) (r κ : ℝ) :
    (ENNReal.ofReal (κ * (Real.sqrt Q * r) ^ n) ≤
      calibratedMetricVolume h (h.ball (f p) (Real.sqrt Q * r))) ↔
    ENNReal.ofReal (κ * r ^ n) ≤ calibratedMetricVolume g (g.ball p r) := by
  have hscale : Real.rpow Q ((n : ℝ) / 2) = Real.sqrt Q ^ n := by
    rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt _ hQ.le, Real.rpow_natCast]
  have hpos : 0 < Real.sqrt Q ^ n := pow_pos (Real.sqrt_pos.mpr hQ) n
  have hne : ENNReal.ofReal (Real.sqrt Q ^ n) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpos).ne'
  rw [← H.ball_image, H.volume_image, hscale, mul_pow]
  rw [show κ * (Real.sqrt Q ^ n * r ^ n) =
    Real.sqrt Q ^ n * (κ * r ^ n) by ring]
  rw [ENNReal.ofReal_mul hpos.le]
  exact ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top

end PoincareConjecture
