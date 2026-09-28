import PoincareConjecture.Proofs.M38.LowerEndReparametrization

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M38

noncomputable def normalScaleProfile (a t : ℝ) : ℝ :=
  a * t + (1 - a) * lowerEndCutoff t * t

theorem normalScaleProfile_inner (a : ℝ) {t : ℝ} (ht : |t| ≤ 1 / 8) :
    normalScaleProfile a t = a * t := by
  rw [normalScaleProfile, lowerEndCutoff_zero ht]
  ring

theorem normalScaleProfile_outer (a : ℝ) {t : ℝ} (ht : 1 / 4 ≤ |t|) :
    normalScaleProfile a t = t := by
  rw [normalScaleProfile, lowerEndCutoff_one ht]
  ring

theorem normalScaleProfile_smooth (a : ℝ) : ContDiff ℝ ∞ (normalScaleProfile a) :=
  (contDiff_const.mul contDiff_id).add
    ((contDiff_const.mul lowerEndCutoff_smooth).mul contDiff_id)

theorem normalScaleProfile_deriv_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (t : ℝ) :
    0 < deriv (normalScaleProfile a) t := by
  have hd := ((hasDerivAt_id t).const_mul a).add
    (((lowerEndCutoff_hasDerivAt t).const_mul (1 - a)).mul (hasDerivAt_id t))
  change HasDerivAt (normalScaleProfile a) _ t at hd
  have hformula : deriv (normalScaleProfile a) t =
      a + (1 - a) * lowerEndCutoff t +
        (1 - a) * 64 * t ^ 2 * deriv Real.smoothTransition (32 * t ^ 2 - 1) := by
    rw [hd.deriv]
    simp only [id_eq]
    ring
  rw [hformula]
  have hq : 0 ≤ lowerEndCutoff t := Real.smoothTransition.nonneg _
  have hdq : 0 ≤ deriv Real.smoothTransition (32 * t ^ 2 - 1) :=
    Real.smoothTransition.monotone.deriv_nonneg
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg ha (mul_nonneg (sub_nonneg.mpr ha1.le) hq))
    (mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr ha1.le)
      (by norm_num)) (sq_nonneg t)) hdq)

theorem normalScaleProfile_strictMono {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    StrictMono (normalScaleProfile a) :=
  strictMono_of_deriv_pos (normalScaleProfile_deriv_pos ha ha1)

theorem normalScaleProfile_surjective (a : ℝ) :
    Function.Surjective (normalScaleProfile a) := by
  intro y
  let l := min y (-1)
  let r := max y 1
  have hl : l ≤ -1 := min_le_right _ _
  have hr : 1 ≤ r := le_max_right _ _
  have hly : l ≤ y := min_le_left _ _
  have hyr : y ≤ r := le_max_left _ _
  have hfl : normalScaleProfile a l = l := normalScaleProfile_outer a (by
    rw [abs_of_nonpos (by linarith : l ≤ 0)]
    linarith)
  have hfr : normalScaleProfile a r = r := normalScaleProfile_outer a (by
    rw [abs_of_nonneg (by linarith : 0 ≤ r)]
    linarith)
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc (hly.trans hyr)
    (normalScaleProfile_smooth a).continuous.continuousOn
    (show y ∈ Icc (normalScaleProfile a l) (normalScaleProfile a r) by
      rw [hfl, hfr]
      exact ⟨hly, hyr⟩)
  exact ⟨t, ht⟩

noncomputable def normalScaleOrderIso (a : ℝ) (ha : 0 < a) (ha1 : a < 1) : ℝ ≃o ℝ :=
  (normalScaleProfile_strictMono ha ha1).orderIsoOfSurjective _
    (normalScaleProfile_surjective a)

@[simp] theorem normalScaleOrderIso_apply (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (t : ℝ) :
    normalScaleOrderIso a ha ha1 t = normalScaleProfile a t := rfl

theorem normalScaleOrderIso_symm_smooth {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ContDiff ℝ ∞ (normalScaleOrderIso a ha ha1).symm := by
  apply (normalScaleOrderIso a ha ha1).toHomeomorph.contDiff_symm_deriv
    (fun t => (normalScaleProfile_deriv_pos ha ha1 t).ne')
    (fun t => ((normalScaleProfile_smooth a).differentiable (by simp) t).hasDerivAt)
    (normalScaleProfile_smooth a)

theorem normalScaleOrderIso_symm_inner {a t : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ht : |t| ≤ a / 8) : (normalScaleOrderIso a ha ha1).symm t = t / a := by
  apply (normalScaleOrderIso a ha ha1).injective
  rw [OrderIso.apply_symm_apply, normalScaleOrderIso_apply,
    normalScaleProfile_inner a (by
      rw [abs_div, abs_of_pos ha]
      exact (div_le_iff₀ ha).mpr (by linarith))]
  field_simp

end PoincareConjecture.M38
