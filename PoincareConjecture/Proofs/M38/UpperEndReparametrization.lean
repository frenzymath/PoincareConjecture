import PoincareConjecture.Proofs.M38.LowerEndReparametrization
import PoincareConjecture.Proofs.M38.PunctureRadial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped ContDiff

namespace PoincareConjecture.M38

theorem punctureRadialOrderIso_lower (t : ℝ) : t - 1 ≤ punctureRadialOrderIso t := by
  rw [punctureRadialOrderIso_apply, capRadialProfile]
  have h := Real.smoothTransition.nonneg (4 * ((t - 1 / 2) / 2) - 1)
  nlinarith

noncomputable def upperEndRaw (k t : ℝ) : ℝ :=
  k * (punctureRadialOrderIso.symm (t / k) - 1)

noncomputable def upperEndRawInverse (k t : ℝ) : ℝ :=
  k * punctureRadialOrderIso (1 + t / k)

theorem upperEndRaw_smooth (k : ℝ) : ContDiff ℝ ∞ (upperEndRaw k) :=
  contDiff_const.mul
    ((punctureRadialOrderIso_symm_smooth.comp (contDiff_id.div_const k)).sub contDiff_const)

theorem upperEndRawInverse_smooth (k : ℝ) : ContDiff ℝ ∞ (upperEndRawInverse k) :=
  contDiff_const.mul
    (punctureRadialOrderIso_smooth.comp (contDiff_const.add (contDiff_id.div_const k)))

theorem upperEndRaw_strictMono {k : ℝ} (hk : 0 < k) : StrictMono (upperEndRaw k) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left
    (sub_lt_sub_right (punctureRadialOrderIso.symm.strictMono
      ((div_lt_div_iff_of_pos_right hk).mpr hst)) 1) hk

theorem upperEndRaw_left_inverse {k : ℝ} (hk : 0 < k) :
    Function.LeftInverse (upperEndRawInverse k) (upperEndRaw k) := by
  intro t
  change k * punctureRadialOrderIso
    (1 + k * (punctureRadialOrderIso.symm (t / k) - 1) / k) = t
  have harg : 1 + k * (punctureRadialOrderIso.symm (t / k) - 1) / k =
      punctureRadialOrderIso.symm (t / k) := by field_simp [hk.ne']; ring
  rw [harg, OrderIso.apply_symm_apply, mul_div_cancel₀ _ hk.ne']

theorem upperEndRaw_right_inverse {k : ℝ} (hk : 0 < k) :
    Function.LeftInverse (upperEndRaw k) (upperEndRawInverse k) := by
  intro t
  change k * (punctureRadialOrderIso.symm (k * punctureRadialOrderIso (1 + t / k) / k) - 1) = t
  rw [mul_div_cancel_left₀ _ hk.ne', OrderIso.symm_apply_apply]
  field_simp [hk.ne']
  ring

theorem upperEndRaw_deriv_pos {k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < deriv (upperEndRaw k) t := by
  have hnonneg : 0 ≤ deriv (upperEndRaw k) t := (upperEndRaw_strictMono hk).monotone.deriv_nonneg
  have h := (((upperEndRawInverse_smooth k).differentiable (by simp)
    (upperEndRaw k t)).hasDerivAt.comp t
      (((upperEndRaw_smooth k).differentiable (by simp)) t).hasDerivAt).deriv
  have hcomp : upperEndRawInverse k ∘ upperEndRaw k = id :=
    funext (upperEndRaw_left_inverse hk)
  rw [hcomp, deriv_id] at h
  by_contra hnot
  have hzero : deriv (upperEndRaw k) t = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  simp only [hzero, mul_zero, one_ne_zero] at h

theorem upperEndRaw_le_self {k : ℝ} (hk : 0 < k) (t : ℝ) : upperEndRaw k t ≤ t := by
  have h := punctureRadialOrderIso_lower (punctureRadialOrderIso.symm (t / k))
  rw [OrderIso.apply_symm_apply] at h
  have hmul := mul_le_mul_of_nonneg_left h hk.le
  simpa only [upperEndRaw, mul_div_cancel₀ _ hk.ne'] using hmul

theorem upperEndRaw_nonpos {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : t ≤ 0) :
    upperEndRaw k t = t := by
  have hinv : punctureRadialOrderIso.symm (t / k) = 1 + t / k := by
    apply punctureRadialOrderIso.injective
    rw [OrderIso.apply_symm_apply,
      punctureRadialOrderIso_sub_one _ (by
        have hdiv : t / k ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht hk.le
        linarith)]
    ring
  rw [upperEndRaw, hinv]
  field_simp [hk.ne']
  ring

noncomputable def upperEndCutoff (t : ℝ) : ℝ := Real.smoothTransition (8 * t - 1)

noncomputable def upperEndProfile (k t : ℝ) : ℝ :=
  (1 - upperEndCutoff t) * upperEndRaw k t + upperEndCutoff t * t

theorem upperEndCutoff_smooth : ContDiff ℝ ∞ upperEndCutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem upperEndCutoff_monotone : Monotone upperEndCutoff := by
  intro s t hst
  exact Real.smoothTransition.monotone (by linarith)

theorem upperEndProfile_inner (k : ℝ) {t : ℝ} (ht : t ≤ 1 / 8) :
    upperEndProfile k t = upperEndRaw k t := by
  have hq : upperEndCutoff t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [upperEndProfile, hq]
  ring

theorem upperEndProfile_outer (k : ℝ) {t : ℝ} (ht : 1 / 4 ≤ t) :
    upperEndProfile k t = t := by
  have hq : upperEndCutoff t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  rw [upperEndProfile, hq]
  ring

theorem upperEndProfile_nonpos {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : t ≤ 0) :
    upperEndProfile k t = t := by
  rw [upperEndProfile_inner k (by linarith), upperEndRaw_nonpos hk ht]

theorem upperEndProfile_smooth (k : ℝ) : ContDiff ℝ ∞ (upperEndProfile k) :=
  ((contDiff_const.sub upperEndCutoff_smooth).mul (upperEndRaw_smooth k)).add
    (upperEndCutoff_smooth.mul contDiff_id)

theorem upperEndProfile_deriv_formula (k t : ℝ) :
    deriv (upperEndProfile k) t =
      (1 - upperEndCutoff t) * deriv (upperEndRaw k) t + upperEndCutoff t +
        deriv upperEndCutoff t * (t - upperEndRaw k t) := by
  have hq := (upperEndCutoff_smooth.differentiable (by simp) t).hasDerivAt
  have hr := ((upperEndRaw_smooth k).differentiable (by simp) t).hasDerivAt
  have h := (((hasDerivAt_const t 1).sub hq).mul hr).add (hq.mul (hasDerivAt_id t))
  change HasDerivAt (upperEndProfile k) _ t at h
  rw [h.deriv]
  simp only [id_eq, Pi.sub_apply, mul_one, zero_sub]
  ring

theorem upperEndProfile_deriv_pos {k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < deriv (upperEndProfile k) t := by
  rw [upperEndProfile_deriv_formula]
  have hq0 : 0 ≤ upperEndCutoff t := Real.smoothTransition.nonneg _
  have hq1 : upperEndCutoff t ≤ 1 := Real.smoothTransition.le_one _
  have hraw := upperEndRaw_deriv_pos hk t
  have hmain : 0 < (1 - upperEndCutoff t) * deriv (upperEndRaw k) t + upperEndCutoff t := by
    by_cases hq : upperEndCutoff t = 1
    · rw [hq]
      norm_num
    · have hq' : 0 < 1 - upperEndCutoff t := by
        rcases hq1.eq_or_lt with h | h
        · exact False.elim (hq h)
        · exact sub_pos.mpr h
      exact add_pos_of_pos_of_nonneg (mul_pos hq' hraw) hq0
  exact add_pos_of_pos_of_nonneg hmain
    (mul_nonneg upperEndCutoff_monotone.deriv_nonneg
      (sub_nonneg.mpr (upperEndRaw_le_self hk t)))

theorem upperEndProfile_strictMono {k : ℝ} (hk : 0 < k) : StrictMono (upperEndProfile k) :=
  strictMono_of_deriv_pos (upperEndProfile_deriv_pos hk)

theorem upperEndProfile_surjective {k : ℝ} (hk : 0 < k) : Function.Surjective (upperEndProfile k) := by
  intro y
  let a : ℝ := min y (-1)
  let b : ℝ := max y 1
  have ha : a ≤ -1 := min_le_right _ _
  have hb : 1 ≤ b := le_max_right _ _
  have hay : a ≤ y := min_le_left _ _
  have hyb : y ≤ b := le_max_left _ _
  have hfa : upperEndProfile k a = a := upperEndProfile_nonpos hk (by linarith)
  have hfb : upperEndProfile k b = b := upperEndProfile_outer k (by linarith)
  obtain ⟨t, _, hty⟩ := intermediate_value_Icc (hay.trans hyb)
    (upperEndProfile_smooth k).continuous.continuousOn
      (show y ∈ Set.Icc (upperEndProfile k a) (upperEndProfile k b) by
        rw [hfa, hfb]
        exact ⟨hay, hyb⟩)
  exact ⟨t, hty⟩

noncomputable def upperEndOrderIso (k : ℝ) (hk : 0 < k) : ℝ ≃o ℝ :=
  (upperEndProfile_strictMono hk).orderIsoOfSurjective _ (upperEndProfile_surjective hk)

@[simp] theorem upperEndOrderIso_apply (k : ℝ) (hk : 0 < k) (t : ℝ) :
    upperEndOrderIso k hk t = upperEndProfile k t := rfl

theorem upperEndOrderIso_symm_smooth {k : ℝ} (hk : 0 < k) :
    ContDiff ℝ ∞ (upperEndOrderIso k hk).symm := by
  apply (upperEndOrderIso k hk).toHomeomorph.contDiff_symm_deriv
    (fun t => (upperEndProfile_deriv_pos hk t).ne')
    (fun t => ((upperEndProfile_smooth k).differentiable (by simp) t).hasDerivAt)
    (upperEndProfile_smooth k)

@[simp] theorem upperEndOrderIso_zero (k : ℝ) (hk : 0 < k) : upperEndOrderIso k hk 0 = 0 :=
  upperEndProfile_nonpos hk le_rfl

@[simp] theorem upperEndOrderIso_one (k : ℝ) (hk : 0 < k) : upperEndOrderIso k hk 1 = 1 :=
  upperEndProfile_outer k (by norm_num)

end PoincareConjecture.M38
