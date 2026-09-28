import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.ComparisonRadius
import Mathlib.Analysis.InnerProductSpace.Basic











noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.ODE.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



theorem inner_ge_half_of_remainders {u z w : E} {t : ℝ} (ht : 0 ≤ t)
    (hu : ‖u - w‖ ≤ ‖w‖ / 8) (hz : ‖z - t • w‖ ≤ t * ‖w‖ / 8) :
    t * ‖w‖ ^ 2 / 2 ≤ inner ℝ u z := by
  have hnz : ‖z‖ ≤ 9 * t * ‖w‖ / 8 := by
    have h := norm_add_le (z - t • w) (t • w)
    rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at h
    linarith
  have h₁ := neg_le_of_abs_le (abs_real_inner_le_norm (u - w) z)
  have h₂ := neg_le_of_abs_le (abs_real_inner_le_norm w (z - t • w))
  have hprod₁ : ‖u - w‖ * ‖z‖ ≤ (‖w‖ / 8) * (9 * t * ‖w‖ / 8) :=
    mul_le_mul hu hnz (norm_nonneg _) (by positivity)
  have hprod₂ : ‖w‖ * ‖z - t • w‖ ≤ ‖w‖ * (t * ‖w‖ / 8) :=
    mul_le_mul_of_nonneg_left hz (norm_nonneg _)
  rw [inner_sub_left] at h₁
  rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at h₂
  nlinarith [mul_nonneg ht (sq_nonneg ‖w‖)]

namespace IsJacobiSolOn

variable [CompleteSpace E]
variable {R : ℝ → E →L[ℝ] E} {b C : ℝ} {y v : ℝ → E}



theorem half_inner_lower_bound (h : IsJacobiSolOn R 0 b y v)
    (hR : ContinuousOn R (Icc 0 b)) (hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ C)
    (hy0 : y 0 = 0) {t : ℝ} (ht : t ∈ Icc 0 b)
    (hsmall : C * Real.exp (max 1 C * b) * t ^ 2 ≤ 1 / 4) :
    t * ‖v 0‖ ^ 2 / 2 ≤ inner ℝ (v t) (y t) := by
  have hv := h.norm_snd_sub_le hR hC hy0 t ht
  have hy := h.norm_fst_sub_le hR hC hy0 t ht
  have hvsmall := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (v 0))
  have hysmall := mul_le_mul_of_nonneg_right hvsmall ht.1
  apply inner_ge_half_of_remainders ht.1
  · nlinarith only [hv, hvsmall]
  · nlinarith [hy, hysmall, mul_nonneg ht.1 (norm_nonneg (v 0))]



theorem inner_pos (h : IsJacobiSolOn R 0 b y v)
    (hR : ContinuousOn R (Icc 0 b)) (hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ C)
    (hy0 : y 0 = 0) {t : ℝ} (ht : t ∈ Icc 0 b) (htpos : 0 < t)
    (hv0 : v 0 ≠ 0)
    (hsmall : C * Real.exp (max 1 C * b) * t ^ 2 ≤ 1 / 4) :
    0 < inner ℝ (v t) (y t) := by
  have hbound := h.half_inner_lower_bound hR hC hy0 ht hsmall
  exact lt_of_lt_of_le (by positivity) hbound

end IsJacobiSolOn



theorem quarter_comparisonRadius_pairing_smallness {K c t : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hcr : c ≤ comparisonRadius K / 4)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (K * c ^ 2) * Real.exp (max 1 (K * c ^ 2)) * t ^ 2 ≤ 1 / 4 := by
  have hfour : 4 * c ≤ comparisonRadius K := by linarith
  have hsmall := comparisonRadius_smallness hK (by positivity : 0 ≤ 4 * c) hfour ht
  have hcoeff : K * c ^ 2 ≤ K * (4 * c) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg c]) hK
  have hexp : Real.exp (max 1 (K * c ^ 2)) ≤
      Real.exp (max 1 (K * (4 * c) ^ 2)) :=
    Real.exp_le_exp.mpr (max_le_max le_rfl hcoeff)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp (mul_nonneg hK (sq_nonneg c))) (sq_nonneg t)
  nlinarith only [hsmall, h]

namespace IsJacobiSolOn

variable [CompleteSpace E]
variable {R : ℝ → E →L[ℝ] E} {y v : ℝ → E} {K c : ℝ}



theorem half_inner_lower_bound_of_speed_le_quarter_comparisonRadius
    (h : IsJacobiSolOn R 0 1 y v) (hR : ContinuousOn R (Icc 0 1))
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hcr : c ≤ comparisonRadius K / 4)
    (hbound : ∀ s ∈ Icc 0 1, ‖R s‖ ≤ K * c ^ 2) (hy0 : y 0 = 0)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    t * ‖v 0‖ ^ 2 / 2 ≤ inner ℝ (v t) (y t) := by
  apply h.half_inner_lower_bound hR hbound hy0 ht
  simpa only [mul_one] using quarter_comparisonRadius_pairing_smallness hK hc hcr ht


theorem half_inner_one_lower_bound_of_speed_le_quarter_comparisonRadius
    (h : IsJacobiSolOn R 0 1 y v) (hR : ContinuousOn R (Icc 0 1))
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hcr : c ≤ comparisonRadius K / 4)
    (hbound : ∀ s ∈ Icc 0 1, ‖R s‖ ≤ K * c ^ 2) (hy0 : y 0 = 0) :
    ‖v 0‖ ^ 2 / 2 ≤ inner ℝ (v 1) (y 1) := by
  simpa only [one_mul] using
    h.half_inner_lower_bound_of_speed_le_quarter_comparisonRadius hR hK hc hcr
      hbound hy0 (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)

end IsJacobiSolOn

end Poincare.ODE.Jacobi
