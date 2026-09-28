






import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith









set_option autoImplicit false

namespace Poincare.ODE.Jacobi

open Set

theorem half_norm_lower_bound_of_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J v : E} {C B t : ℝ}
    (hrem : ‖J - t • v‖ ≤ C * ‖v‖ * B * t ^ 3 / 6)
    (ht : 0 ≤ t) (hsmall : C * B * t ^ 2 ≤ 3) :
    t * ‖v‖ / 2 ≤ ‖J‖ := by
  have htri : ‖t • v‖ ≤ ‖J‖ + ‖J - t • v‖ := by
    calc
      ‖t • v‖ = ‖J - (J - t • v)‖ := by congr 1; abel
      _ ≤ ‖J‖ + ‖J - t • v‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at htri
  have hnonneg : 0 ≤ ‖v‖ := norm_nonneg v
  have hmul := mul_le_mul_of_nonneg_right hsmall hnonneg
  nlinarith [hrem, htri, hmul]


theorem norm_sub_linear_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {R : ℝ → E →L[ℝ] E} {y v : ℝ → E} {b C : ℝ}
    (h : IsJacobiSolOn R 0 b y v) (hR : ContinuousOn R (Icc 0 b))
    (hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ C) (hy0 : y 0 = 0)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    ‖y t - t • v 0‖ ≤ C * ‖v 0‖ * Real.exp (max 1 C * b) * t ^ 3 / 6 := by
  simpa [mul_assoc] using h.norm_fst_sub_le hR hC hy0 t ht


theorem jacobi_norm_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {R : ℝ → E →L[ℝ] E} {y v : ℝ → E} {b C : ℝ}
    (h : IsJacobiSolOn R 0 b y v) (hR : ContinuousOn R (Icc 0 b))
    (hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ C) (hy0 : y 0 = 0)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    (1 - C * Real.exp (max 1 C * b) * t ^ 2 / 6) * t * ‖v 0‖ ≤ ‖y t‖ := by
  have hrem := norm_sub_linear_le h hR hC hy0 ht
  have htri := norm_sub_norm_le (t • v 0) (y t)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, norm_sub_rev] at htri
  nlinarith only [hrem, htri]


theorem half_norm_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {R : ℝ → E →L[ℝ] E} {y v : ℝ → E} {b C : ℝ}
    (h : IsJacobiSolOn R 0 b y v) (hR : ContinuousOn R (Icc 0 b))
    (hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ C) (hy0 : y 0 = 0)
    {t : ℝ} (ht : t ∈ Icc 0 b)
    (hsmall : C * Real.exp (max 1 C * b) * t ^ 2 ≤ 3) :
    t * ‖v 0‖ / 2 ≤ ‖y t‖ := by
  exact half_norm_lower_bound_of_remainder (norm_sub_linear_le h hR hC hy0 ht)
    ht.1 hsmall

end Poincare.ODE.Jacobi
