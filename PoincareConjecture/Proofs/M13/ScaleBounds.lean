import PoincareConjecture.Statements.M13ScaleBounds
import PoincareConjecture.Proofs.M13.Time








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem parabolicScaleBounds (P : ParabolicSpacetimeRescaling R Q hQ a)
    (H : ParabolicHorizontalCalculus P) : ParabolicScaleBounds P where
  curvature_bound D D' E K := by
    simp only [H.norm_eq D D', div_le_div_iff_of_pos_right hQ]
  parabolic_curvature_bound D D' E r _hr := by
    have hradius : 1 / (Real.sqrt Q * r) ^ 2 = (1 / r ^ 2) / Q := by
      rw [mul_pow, Real.sq_sqrt hQ.le, div_div, mul_comm]
    simp only [H.norm_eq D D', hradius, div_le_div_iff_of_pos_right hQ]
  volume_bound t x r κ _hr _hκ := by
    have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
    have hfactor : Real.rpow Q ((n : ℝ) / 2) = Real.sqrt Q ^ n := by
      rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt (n : ℝ) hQ.le, Real.rpow_natCast]
    have hvolume := (H.slice_calculus t).volume_image ((R.slices t).metricOnPoints.ball x r)
    rw [(H.slice_calculus t).ball_image] at hvolume
    rw [hvolume, hfactor]
    have hleft : ENNReal.ofReal (κ * (Real.sqrt Q * r) ^ n) =
        ENNReal.ofReal (Real.sqrt Q ^ n) * ENNReal.ofReal (κ * r ^ n) := by
      rw [mul_pow]
      have heq : κ * (Real.sqrt Q ^ n * r ^ n) = Real.sqrt Q ^ n * (κ * r ^ n) := by ring
      rw [heq, ENNReal.ofReal_mul (pow_nonneg hs.le n)]
    rw [hleft]
    exact ENNReal.mul_le_mul_iff_right
      (ENNReal.ofReal_pos.mpr (pow_pos hs n)).ne' ENNReal.ofReal_ne_top
  scale_cutoff r r₀ := by
    have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
    simp only [mul_pos_iff_of_pos_left hs, mul_le_mul_iff_right₀ hs]
  base_normalization D D' p hscalar htime := by
    constructor
    · change P.atlasRescaling.atlas.time p = 0
      rw [P.atlasRescaling.time_eq]
      change parabolicTime Q a (R.spacetime.timeFunction p) = 0
      rw [← htime]
      simp only [parabolicTime, sub_self, mul_zero]
    · rw [H.scalar_eq D D' p, ← hscalar, div_self hQ.ne']

end PoincareConjecture.M13
