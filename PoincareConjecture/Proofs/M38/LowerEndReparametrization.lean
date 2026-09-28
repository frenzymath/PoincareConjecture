import PoincareConjecture.Proofs.M38.BallShrinking
import Mathlib.Analysis.Calculus.Deriv.MeanValue









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped ContDiff

namespace PoincareConjecture.M38


noncomputable def lowerEndCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition (32 * t ^ 2 - 1)


noncomputable def lowerEndProfile (k t : ℝ) : ℝ :=
  lowerEndCutoff t * t + (1 - lowerEndCutoff t) * (k * t / (1 - t))


theorem lowerEndCutoff_zero {t : ℝ} (ht : |t| ≤ 1 / 8) : lowerEndCutoff t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h := abs_le.mp ht
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 8 - t)
    (by linarith : 0 ≤ 1 / 8 + t)]


theorem lowerEndCutoff_one {t : ℝ} (ht : 1 / 4 ≤ |t|) : lowerEndCutoff t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  nlinarith [sq_abs t, sq_nonneg (|t| - 1 / 4)]


theorem lowerEndProfile_inner (k : ℝ) {t : ℝ} (ht : |t| ≤ 1 / 8) :
    lowerEndProfile k t = k * t / (1 - t) := by
  rw [lowerEndProfile, lowerEndCutoff_zero ht]
  ring


theorem lowerEndProfile_outer (k : ℝ) {t : ℝ} (ht : 1 / 4 ≤ |t|) :
    lowerEndProfile k t = t := by
  rw [lowerEndProfile, lowerEndCutoff_one ht]
  ring


theorem lowerEndCutoff_smooth : ContDiff ℝ ∞ lowerEndCutoff :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const)


theorem lowerEndProfile_smooth (k : ℝ) : ContDiff ℝ ∞ (lowerEndProfile k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t < 1 / 2
  · have hne : 1 - t ≠ 0 := by linarith
    exact (lowerEndCutoff_smooth.contDiffAt.mul contDiffAt_id).add
      ((contDiffAt_const.sub lowerEndCutoff_smooth.contDiffAt).mul
        ((contDiffAt_const.mul contDiffAt_id).div
          (contDiffAt_const.sub contDiffAt_id) hne))
  · apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds (show 1 / 4 < t by linarith)] with s hs
    exact lowerEndProfile_outer k (le_trans (le_of_lt hs) (le_abs_self s))


theorem lowerEndCutoff_hasDerivAt (t : ℝ) :
    HasDerivAt lowerEndCutoff
      (64 * t * deriv Real.smoothTransition (32 * t ^ 2 - 1)) t := by
  have hST : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have h := ((hST.differentiable (by simp))
    (32 * t ^ 2 - 1)).hasDerivAt.comp t
      ((((hasDerivAt_id t).pow 2).const_mul 32).sub_const 1)
  convert h using 1 <;> first | rfl | (simp only [id_eq, Pi.pow_apply]; ring)


theorem lowerEndProfile_deriv_formula (k : ℝ) {t : ℝ} (ht : t < 1 / 2) :
    deriv (lowerEndProfile k) t =
      lowerEndCutoff t + (1 - lowerEndCutoff t) * (k / (1 - t) ^ 2) +
        64 * deriv Real.smoothTransition (32 * t ^ 2 - 1) * t ^ 2 *
          ((1 - t - k) / (1 - t)) := by
  have hne : 1 - t ≠ 0 := by linarith
  have hr : HasDerivAt (fun s : ℝ => k * s / (1 - s)) (k / (1 - t) ^ 2) t := by
    convert ((hasDerivAt_id t).const_mul k).div
      ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) hne using 1 <;>
        first | rfl | (simp only [id_eq, Pi.sub_apply]; field_simp [hne]; ring)
  have hq := lowerEndCutoff_hasDerivAt t
  have h := (hq.mul (hasDerivAt_id t)).add
    (((hasDerivAt_const t 1).sub hq).mul hr)
  change HasDerivAt (lowerEndProfile k) _ t at h
  rw [h.deriv]
  simp only [id_eq, Pi.sub_apply, mul_one, zero_sub]
  field_simp [hne]
  ring


theorem lowerEndProfile_deriv_pos {k : ℝ} (hk : 0 < k) (hk2 : k ≤ 1 / 2) (t : ℝ) :
    0 < deriv (lowerEndProfile k) t := by
  by_cases ht : t < 1 / 2
  · rw [lowerEndProfile_deriv_formula k ht]
    have hq0 : 0 ≤ lowerEndCutoff t := Real.smoothTransition.nonneg _
    have hq1 : lowerEndCutoff t ≤ 1 := Real.smoothTransition.le_one _
    have hden : 0 < 1 - t := by linarith
    have hrat : 0 < k / (1 - t) ^ 2 := div_pos hk (sq_pos_of_pos hden)
    have hmain : 0 < lowerEndCutoff t +
        (1 - lowerEndCutoff t) * (k / (1 - t) ^ 2) := by
      by_cases hq : lowerEndCutoff t = 1
      · rw [hq]
        norm_num
      · have hq' : 0 < 1 - lowerEndCutoff t := by
          rcases hq1.eq_or_lt with h | h
          · exact False.elim (hq h)
          · exact sub_pos.mpr h
        exact add_pos_of_nonneg_of_pos hq0 (mul_pos hq' hrat)
    apply add_pos_of_pos_of_nonneg hmain
    have hderiv : 0 ≤ deriv Real.smoothTransition (32 * t ^ 2 - 1) :=
      Real.smoothTransition.monotone.deriv_nonneg
    have hnum : 0 ≤ 1 - t - k := by linarith
    positivity
  · have h : HasDerivAt (lowerEndProfile k) 1 t := by
      apply (hasDerivAt_id t).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds (show 1 / 4 < t by linarith)] with s hs
      exact lowerEndProfile_outer k (le_trans (le_of_lt hs) (le_abs_self s))
    rw [h.deriv]
    norm_num


theorem lowerEndProfile_strictMono {k : ℝ} (hk : 0 < k) (hk2 : k ≤ 1 / 2) :
    StrictMono (lowerEndProfile k) :=
  strictMono_of_deriv_pos (lowerEndProfile_deriv_pos hk hk2)


theorem lowerEndProfile_surjective (k : ℝ) : Function.Surjective (lowerEndProfile k) := by
  intro y
  let a : ℝ := min y (-1)
  let b : ℝ := max y 1
  have ha : a ≤ -1 := min_le_right _ _
  have hb : 1 ≤ b := le_max_right _ _
  have hay : a ≤ y := min_le_left _ _
  have hyb : y ≤ b := le_max_left _ _
  have hfa : lowerEndProfile k a = a := lowerEndProfile_outer k (by
    rw [abs_of_nonpos (by linarith : a ≤ 0)]
    linarith)
  have hfb : lowerEndProfile k b = b := lowerEndProfile_outer k (by
    rw [abs_of_nonneg (by linarith : 0 ≤ b)]
    linarith)
  obtain ⟨t, _, hty⟩ := intermediate_value_Icc (hay.trans hyb)
    (lowerEndProfile_smooth k).continuous.continuousOn
      (show y ∈ Set.Icc (lowerEndProfile k a) (lowerEndProfile k b) by
        rw [hfa, hfb]
        exact ⟨hay, hyb⟩)
  exact ⟨t, hty⟩


noncomputable def lowerEndOrderIso (k : ℝ) (hk : 0 < k) (hk2 : k ≤ 1 / 2) : ℝ ≃o ℝ :=
  (lowerEndProfile_strictMono hk hk2).orderIsoOfSurjective _ (lowerEndProfile_surjective k)


@[simp] theorem lowerEndOrderIso_apply (k : ℝ) (hk : 0 < k) (hk2 : k ≤ 1 / 2) (t : ℝ) :
    lowerEndOrderIso k hk hk2 t = lowerEndProfile k t := rfl


theorem lowerEndOrderIso_symm_smooth {k : ℝ} (hk : 0 < k) (hk2 : k ≤ 1 / 2) :
    ContDiff ℝ ∞ (lowerEndOrderIso k hk hk2).symm := by
  apply (lowerEndOrderIso k hk hk2).toHomeomorph.contDiff_symm_deriv
    (fun t => (lowerEndProfile_deriv_pos hk hk2 t).ne')
    (fun t => ((lowerEndProfile_smooth k).differentiable (by simp) t).hasDerivAt)
    (lowerEndProfile_smooth k)


@[simp] theorem lowerEndOrderIso_zero (k : ℝ) (hk : 0 < k) (hk2 : k ≤ 1 / 2) :
    lowerEndOrderIso k hk hk2 0 = 0 := by
  rw [lowerEndOrderIso_apply, lowerEndProfile_inner k (by norm_num : |(0 : ℝ)| ≤ 1 / 8)]
  norm_num


@[simp] theorem lowerEndOrderIso_one (k : ℝ) (hk : 0 < k) (hk2 : k ≤ 1 / 2) :
    lowerEndOrderIso k hk hk2 1 = 1 :=
  lowerEndProfile_outer k (by norm_num)

end PoincareConjecture.M38
