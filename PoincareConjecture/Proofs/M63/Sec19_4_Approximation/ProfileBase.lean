import PoincareConjecture.Statements.M63Polygon
import PoincareConjecture.Proofs.M63.Mathlib.ExpNegInvGlueProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false

open scoped ContDiff intervalIntegral

namespace PoincareConjecture

theorem m63CellLength_pos {N : ℕ} (hN : 0 < N) : 0 < m63CellLength N := by
  exact div_pos (show 0 < curvePeriod from Real.two_pi_pos) (Nat.cast_pos.mpr hN)

theorem m63_count_mul_cellLength {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * m63CellLength N = 2 * Real.pi := by
  dsimp [m63CellLength, curvePeriod]
  field_simp

theorem m63ProfileBase_smooth (N : ℕ) : ContDiff ℝ ∞ (m63ProfileBase N) := by
  exact expNegInvGlue.contDiff.comp
    (contDiff_const.sub ((contDiff_const.mul contDiff_id).cos))

theorem m63ProfileBase_nonneg (N : ℕ) (x : ℝ) : 0 ≤ m63ProfileBase N x :=
  expNegInvGlue.nonneg _

theorem m63ProfileBase_pos {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (m63CellLength N)) : 0 < m63ProfileBase N x := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hx0 : 0 < (N : ℝ) * x := mul_pos hNr hx.1
  have hx1 : (N : ℝ) * x < 2 * Real.pi := by
    calc
      (N : ℝ) * x < (N : ℝ) * m63CellLength N := mul_lt_mul_of_pos_left hx.2 hNr
      _ = 2 * Real.pi := m63_count_mul_cellLength hN
  apply expNegInvGlue.pos_of_pos
  apply sub_pos.mpr
  exact lt_of_le_of_ne (Real.cos_le_one _) (fun h =>
    hx0.ne' ((Real.cos_eq_one_iff_of_lt_of_lt
      (by linarith [Real.pi_pos]) hx1).mp h))

theorem m63ProfileBase_periodic {N : ℕ} (hN : 0 < N) :
    Function.Periodic (m63ProfileBase N) (m63CellLength N) := by
  intro x
  simp only [m63ProfileBase, mul_add, m63_count_mul_cellLength hN, Real.cos_add_two_pi]

theorem m63ProfileBase_symmetric {N : ℕ} (hN : 0 < N) (x : ℝ) :
    m63ProfileBase N (m63CellLength N - x) = m63ProfileBase N x := by
  simp only [m63ProfileBase, mul_sub, m63_count_mul_cellLength hN, Real.cos_two_pi_sub]

theorem m63ProfileBase_monotone_half {N : ℕ} (hN : 0 < N) :
    MonotoneOn (m63ProfileBase N) (Set.Icc 0 (m63CellLength N / 2)) := by
  intro x hx y hy hxy
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  apply expNegInvGlue.monotone
  apply sub_le_sub_left
  apply Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hNr hx.1)
  · have h := mul_le_mul_of_nonneg_left hy.2 hNr
    have heq := m63_count_mul_cellLength hN
    nlinarith
  · exact mul_le_mul_of_nonneg_left hxy hNr

theorem m63ProfileBase_integral_pos {N : ℕ} (hN : 0 < N) :
    0 < ∫ x in (0 : ℝ)..m63CellLength N, m63ProfileBase N x := by
  have hell := m63CellLength_pos hN
  apply intervalIntegral.integral_pos hell (m63ProfileBase_smooth N).continuous.continuousOn
    (fun x _ => m63ProfileBase_nonneg N x)
  refine ⟨m63CellLength N / 2, ⟨by linarith, by linarith⟩, ?_⟩
  exact m63ProfileBase_pos hN ⟨by linarith, by linarith⟩

theorem m63Profile_smooth (N : ℕ) : ContDiff ℝ ∞ (m63Profile N) := by
  exact (contDiff_const.mul (m63ProfileBase_smooth N)).div_const _

theorem m63Profile_periodic {N : ℕ} (hN : 0 < N) :
    Function.Periodic (m63Profile N) (m63CellLength N) := by
  intro x
  simp only [m63Profile, m63ProfileBase_periodic hN x]

theorem m63Profile_nonneg {N : ℕ} (hN : 0 < N) (x : ℝ) : 0 ≤ m63Profile N x := by
  exact div_nonneg (mul_nonneg (m63CellLength_pos hN).le (m63ProfileBase_nonneg N x))
    (m63ProfileBase_integral_pos hN).le

theorem m63Profile_pos {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (m63CellLength N)) : 0 < m63Profile N x := by
  exact div_pos (mul_pos (m63CellLength_pos hN) (m63ProfileBase_pos hN hx))
    (m63ProfileBase_integral_pos hN)

theorem m63Profile_symmetric {N : ℕ} (hN : 0 < N) (x : ℝ) :
    m63Profile N (m63CellLength N - x) = m63Profile N x := by
  simp only [m63Profile, m63ProfileBase_symmetric hN x]

theorem m63Profile_monotone_half {N : ℕ} (hN : 0 < N) :
    MonotoneOn (m63Profile N) (Set.Icc 0 (m63CellLength N / 2)) := by
  intro x hx y hy hxy
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (m63ProfileBase_monotone_half hN hx hy hxy)
      (m63CellLength_pos hN).le) (m63ProfileBase_integral_pos hN).le

theorem m63Profile_cell_integral {N : ℕ} (hN : 0 < N) :
    (∫ x in (0 : ℝ)..m63CellLength N, m63Profile N x) = m63CellLength N := by
  simp only [m63Profile, intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  exact mul_div_cancel_right₀ _ (m63ProfileBase_integral_pos hN).ne'

theorem m63Profile_flat {N : ℕ} (hN : 0 < N) (i : ℕ) (j : ℤ) :
    iteratedDeriv i (m63Profile N) ((j : ℝ) * m63CellLength N) = 0 := by
  have harg : (N : ℝ) * ((j : ℝ) * m63CellLength N) = (j : ℝ) * (2 * Real.pi) := by
    rw [mul_left_comm, m63_count_mul_cellLength hN]
  have hbase : iteratedDeriv i (m63ProfileBase N) ((j : ℝ) * m63CellLength N) = 0 := by
    apply expNegInvGlue.iteratedDeriv_comp_zero (f := fun x => 1 - Real.cos ((N : ℝ) * x))
      (contDiff_const.sub ((contDiff_const.mul contDiff_id).cos)).contDiffAt
    simp only [harg, Real.cos_int_mul_two_pi, sub_self]
  unfold m63Profile
  rw [iteratedDeriv_div_const, iteratedDeriv_const_mul_field, hbase, mul_zero, zero_div]

end PoincareConjecture
