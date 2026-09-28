import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialScalar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M47

private theorem initial_birth_scalar_factors
    {R d gamma : ℝ} (hR : 0 < R) (hd : 0 ≤ d)
    (hgamma : 0 < gamma) (hsmall : gamma ≤ 1 / 1200) (hshort : d < 1 + gamma)
    (herror : |1 / R - 1 / (1 + d)| ≤ (16 / 5 : ℝ) * gamma) :
    (99 / 100 : ℝ) < R ∧ R < 81 / 40 ∧
      1 / R ≤ (101 / 100 : ℝ) ∧ (1 + d) / R ≤ (101 / 100 : ℝ) := by
  have hden : 0 < 1 + d := by linarith
  have hdenUpper : 1 + d < (2401 / 1200 : ℝ) := by linarith
  have herrorUpper : (16 / 5 : ℝ) * gamma ≤ 1 / 375 := by linarith
  have hreciprocalUpper : 1 / (1 + d) ≤ (1 : ℝ) := by
    exact (div_le_iff₀ hden).mpr (by linarith)
  have hreciprocalLower : (1200 / 2401 : ℝ) < 1 / (1 + d) := by
    apply (lt_div_iff₀ hden).mpr
    linarith
  have hupper : 1 / R ≤ (376 / 375 : ℝ) := by
    linarith [(abs_le.mp herror).2]
  have hlower : (40 / 81 : ℝ) < 1 / R := by
    linarith [(abs_le.mp herror).1]
  have hRlower : (99 / 100 : ℝ) < R := by
    have h := (div_le_iff₀ hR).mp hupper
    linarith
  have hRupper : R < (81 / 40 : ℝ) := by
    have h := (lt_div_iff₀ hR).mp hlower
    linarith
  refine ⟨hRlower, hRupper, hupper.trans (by norm_num), ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left (abs_le.mp herror).2 hden.le
  have hcancel : (1 + d) * (1 / (1 + d)) = 1 := by field_simp
  rw [mul_sub, hcancel] at hscaled
  have hproduct : (1 + d) * ((16 / 5 : ℝ) * gamma) ≤
      (2401 / 1200 : ℝ) * (1 / 375) :=
    mul_le_mul hdenUpper.le herrorUpper (by positivity) (by norm_num)
  rw [div_eq_mul_inv, ← one_mul R⁻¹] at hscaled
  simpa only [div_eq_mul_inv] using
    (show (1 + d) * R⁻¹ ≤ (101 / 100 : ℝ) by linarith)

theorem standard_initial_neck_birth_scale_bounds
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z
      (Icc (-v * (G.connection v).scalarCurvature z) 0))
    (hsmall : gamma ≤ 1 / 1200)
    (hdisjoint : Disjoint N.patch.carrier
      {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
    (hshort : v * (G.connection v).scalarCurvature z < 1 + gamma) :
    (99 / 100 : ℝ) < (G.connection v).scalarCurvature z ∧
      (G.connection v).scalarCurvature z < (81 / 40 : ℝ) ∧
      1 / (G.connection v).scalarCurvature z ≤ (101 / 100 : ℝ) ∧
      (1 + v * (G.connection v).scalarCurvature z) /
        (G.connection v).scalarCurvature z ≤ (101 / 100 : ℝ) := by
  have herror := (standard_initial_neck_birth_scale_lt_four N
    (by linarith) hdisjoint hshort).1
  exact initial_birth_scalar_factors N.scalar_pos
    (mul_nonneg N.time_mem.1 N.scalar_pos.le) N.epsilon_pos hsmall hshort herror

end PoincareConjecture.M47
