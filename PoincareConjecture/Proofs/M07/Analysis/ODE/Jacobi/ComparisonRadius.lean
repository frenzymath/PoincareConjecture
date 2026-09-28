import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.LowerBound










noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.ODE.Jacobi



def comparisonRadius (K : ℝ) : ℝ :=
  (2 + max K 0 * Real.exp (max K 0 + 1))⁻¹

theorem comparisonRadius_pos (K : ℝ) : 0 < comparisonRadius K := by
  unfold comparisonRadius
  positivity

theorem comparisonRadius_le_half (K : ℝ) : comparisonRadius K ≤ 1 / 2 := by
  unfold comparisonRadius
  rw [inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  exact le_add_of_nonneg_right (mul_nonneg (le_max_right K 0) (Real.exp_pos _).le)

theorem curvature_mul_sq_le_one_of_le_comparisonRadius {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hcr : c ≤ comparisonRadius K) : K * c ^ 2 ≤ 1 := by
  have hr : 0 ≤ comparisonRadius K := (comparisonRadius_pos K).le
  have hc1 : c ≤ 1 := hcr.trans ((comparisonRadius_le_half K).trans (by norm_num))
  have hcsq : c ^ 2 ≤ comparisonRadius K := le_trans (by nlinarith) hcr
  have hden : 0 < 2 + K * Real.exp (K + 1) := by positivity
  have hmul : comparisonRadius K * (2 + K * Real.exp (K + 1)) = 1 := by
    simp only [comparisonRadius, max_eq_left hK]
    exact inv_mul_cancel₀ hden.ne'
  have hexp : K ≤ K * Real.exp (K + 1) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr (by linarith)) hK
  have hKr : K * comparisonRadius K ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hexp hr]
  exact (mul_le_mul_of_nonneg_left hcsq hK).trans hKr



theorem comparisonRadius_smallness {K c t : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hcr : c ≤ comparisonRadius K) (ht : t ∈ Icc (0 : ℝ) 1) :
    (K * c ^ 2) * Real.exp (max 1 (K * c ^ 2)) * t ^ 2 ≤ 3 := by
  have hr : comparisonRadius K ≤ 1 := (comparisonRadius_le_half K).trans (by norm_num)
  have hc1 : c ≤ 1 := hcr.trans hr
  have hcsq : c ^ 2 ≤ c := by nlinarith
  have hmax : max 1 (K * c ^ 2) ≤ K + 1 := by
    apply max_le
    · linarith
    · nlinarith [mul_le_mul_of_nonneg_left (hcsq.trans hc1) hK]
  have hexp : Real.exp (max 1 (K * c ^ 2)) ≤ Real.exp (K + 1) :=
    Real.exp_le_exp.mpr hmax
  have hrbound : K * comparisonRadius K * Real.exp (K + 1) ≤ 1 := by
    have hden : 0 < 2 + K * Real.exp (K + 1) := by positivity
    have hmul : comparisonRadius K * (2 + K * Real.exp (K + 1)) = 1 := by
      simp only [comparisonRadius, max_eq_left hK]
      exact inv_mul_cancel₀ hden.ne'
    nlinarith [comparisonRadius_pos K]
  have hct : K * c ^ 2 * Real.exp (max 1 (K * c ^ 2)) ≤ 1 := by
    calc
      K * c ^ 2 * Real.exp (max 1 (K * c ^ 2)) ≤
          K * c ^ 2 * Real.exp (K + 1) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hK (sq_nonneg c))
      _ ≤ K * comparisonRadius K * Real.exp (K + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcsq.trans hcr) hK) (Real.exp_pos _).le
      _ ≤ 1 := hrbound
  have htsq : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hnonneg : 0 ≤ K * c ^ 2 * Real.exp (max 1 (K * c ^ 2)) := by positivity
  exact (mul_le_of_le_one_right hnonneg htsq).trans (hct.trans (by norm_num))



theorem half_norm_lower_bound_of_speed_le_comparisonRadius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {R : ℝ → E →L[ℝ] E} {y v : ℝ → E} {K c : ℝ}
    (h : IsJacobiSolOn R 0 1 y v) (hR : ContinuousOn R (Icc 0 1))
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hcr : c ≤ comparisonRadius K)
    (hbound : ∀ s ∈ Icc 0 1, ‖R s‖ ≤ K * c ^ 2) (hy0 : y 0 = 0)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    t * ‖v 0‖ / 2 ≤ ‖y t‖ := by
  apply half_norm_lower_bound h hR hbound hy0 ht
  simpa only [mul_one] using comparisonRadius_smallness hK hc hcr ht



theorem norm_bounds_of_speed_le_comparisonRadius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {R : ℝ → E →L[ℝ] E} {y v : ℝ → E} {K c : ℝ}
    (h : IsJacobiSolOn R 0 1 y v) (hR : ContinuousOn R (Icc 0 1))
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hcr : c ≤ comparisonRadius K)
    (hbound : ∀ s ∈ Icc 0 1, ‖R s‖ ≤ K * c ^ 2) (hy0 : y 0 = 0)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    t * ‖v 0‖ / 2 ≤ ‖y t‖ ∧ ‖y t‖ ≤ Real.exp 1 * t * ‖v 0‖ := by
  refine ⟨half_norm_lower_bound_of_speed_le_comparisonRadius h hR hK hc hcr
    hbound hy0 ht, ?_⟩
  have hunit : ∀ s ∈ Icc 0 1, ‖R s‖ ≤ 1 :=
    fun s hs => (hbound s hs).trans (curvature_mul_sq_le_one_of_le_comparisonRadius hK hc hcr)
  simpa only [max_self, mul_one, mul_comm, mul_left_comm, mul_assoc] using
    h.norm_fst_le hunit hy0 t ht

end Poincare.ODE.Jacobi
