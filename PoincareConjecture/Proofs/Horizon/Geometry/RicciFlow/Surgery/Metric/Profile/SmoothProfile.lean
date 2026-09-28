import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring








set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.MetricSurgery

noncomputable def smoothProfile (C q epsilon s : ℝ) : ℝ :=
  C * epsilon * expNegInvGlue (s / q)

theorem smoothProfile_contDiff (C q epsilon : ℝ) :
    ContDiff ℝ ∞ (smoothProfile C q epsilon) :=
  contDiff_const.mul (expNegInvGlue.contDiff.comp (contDiff_id.div_const q))

theorem smoothProfile_eq_zero {C q epsilon s : ℝ} (hq : 0 < q) (hs : s ≤ 0) :
    smoothProfile C q epsilon s = 0 := by
  rw [smoothProfile, expNegInvGlue.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg hs hq.le), mul_zero]

theorem smoothProfile_eq_exp {C q epsilon s : ℝ} (hq : 0 < q) (hs : 0 < s) :
    smoothProfile C q epsilon s = C * epsilon * Real.exp (-q / s) := by
  have hsq : ¬ s / q ≤ 0 := not_le.mpr (div_pos hs hq)
  simp only [smoothProfile, expNegInvGlue, if_neg hsq, inv_div]
  rw [neg_div]

theorem smoothProfile_nonneg {C q epsilon : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon) (s : ℝ) :
    0 ≤ smoothProfile C q epsilon s :=
  mul_nonneg (mul_nonneg hC hepsilon) (expNegInvGlue.nonneg _)

theorem smoothProfile_pos {C q epsilon s : ℝ}
    (hC : 0 < C) (hq : 0 < q) (hepsilon : 0 < epsilon) (hs : 0 < s) :
    0 < smoothProfile C q epsilon s :=
  mul_pos (mul_pos hC hepsilon) (expNegInvGlue.pos_of_pos (div_pos hs hq))

noncomputable def conformalFactor (C q epsilon s : ℝ) : ℝ :=
  Real.exp (-2 * smoothProfile C q epsilon s)

theorem conformalFactor_contDiff (C q epsilon : ℝ) :
    ContDiff ℝ ∞ (conformalFactor C q epsilon) :=
  (contDiff_const.mul (smoothProfile_contDiff C q epsilon)).exp

theorem conformalFactor_pos (C q epsilon s : ℝ) :
    0 < conformalFactor C q epsilon s := Real.exp_pos _

theorem conformalFactor_le_one {C q epsilon : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon) (s : ℝ) :
    conformalFactor C q epsilon s ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hf := smoothProfile_nonneg (q := q) hC hepsilon s
  linarith

theorem conformalFactor_eq_one {C q epsilon s : ℝ}
    (hq : 0 < q) (hs : s ≤ 0) : conformalFactor C q epsilon s = 1 := by
  simp [conformalFactor, smoothProfile_eq_zero hq hs]

noncomputable def neckCutoff (s : ℝ) : ℝ :=
  1 - Real.smoothTransition (2 * s - 5 / 2)

theorem neckCutoff_contDiff : ContDiff ℝ ∞ neckCutoff :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem neckCutoff_nonneg (s : ℝ) : 0 ≤ neckCutoff s :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem neckCutoff_le_one (s : ℝ) : neckCutoff s ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem neckCutoff_eq_one {s : ℝ} (hs : s ≤ 5 / 4) : neckCutoff s = 1 := by
  rw [neckCutoff, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem neckCutoff_eq_zero {s : ℝ} (hs : 7 / 4 ≤ s) : neckCutoff s = 0 := by
  rw [neckCutoff, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

noncomputable def tipCutoff (A r s : ℝ) : ℝ :=
  1 - Real.smoothTransition (4 * (s - (A - 3 * r / 4)) / r)

theorem tipCutoff_contDiff (A r : ℝ) : ContDiff ℝ ∞ (tipCutoff A r) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.sub contDiff_const)).div_const r))

theorem tipCutoff_nonneg (A r s : ℝ) : 0 ≤ tipCutoff A r s :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem tipCutoff_le_one (A r s : ℝ) : tipCutoff A r s ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem tipCutoff_eq_one {A r s : ℝ} (hr : 0 < r) (hs : s ≤ A - 3 * r / 4) :
    tipCutoff A r s = 1 := by
  rw [tipCutoff, Real.smoothTransition.zero_of_nonpos ?_, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le

theorem tipCutoff_eq_zero {A r s : ℝ} (hr : 0 < r) (hs : A - r / 2 ≤ s) :
    tipCutoff A r s = 0 := by
  rw [tipCutoff, Real.smoothTransition.one_of_one_le ?_, sub_self]
  apply (le_div_iff₀ hr).mpr
  linarith

end PoincareConjecture.MetricSurgery
