import PoincareLib.Topology.Manifold.Surgery.Event.Lower.LowerEndReparametrization
import PoincareLib.Topology.Manifold.Surgery.Event.Puncture.PunctureRadial

/-!
# A supported scalar inverse of the supplied puncture profile

The actual scalar inverse is kept near zero and blended into identity
with an increasing cutoff. The puncture profile's lower bound makes
the cutoff correction nonnegative. No inverse is replaced by a merely
topological choice when smoothness is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped ContDiff

namespace PoincareMT.M38

/-- The actual puncture profile is bounded below by its boundary translation. -/
theorem punctureRadialOrderIso_lower (t : ℝ) : t - 1 ≤ punctureRadialOrderIso t := by
  rw [punctureRadialOrderIso_apply, capRadialProfile]
  have h := Real.smoothTransition.nonneg (4 * ((t - 1 / 2) / 2) - 1)
  nlinarith

/-- The exact scalar change prescribed by the actual upper ball collar. -/
noncomputable def upperEndRaw (k t : ℝ) : ℝ :=
  k * (punctureRadialOrderIso.symm (t / k) - 1)

/-- Its actual inverse uses the original forward puncture profile. -/
noncomputable def upperEndRawInverse (k t : ℝ) : ℝ :=
  k * punctureRadialOrderIso (1 + t / k)

/-- Both literal scalar formulas are globally smooth. -/
theorem upperEndRaw_smooth (k : ℝ) : ContDiff ℝ ∞ (upperEndRaw k) :=
  contDiff_const.mul
    ((punctureRadialOrderIso_symm_smooth.comp (contDiff_id.div_const k)).sub contDiff_const)

/-- The displayed actual inverse is smooth on the entire real line. -/
theorem upperEndRawInverse_smooth (k : ℝ) : ContDiff ℝ ∞ (upperEndRawInverse k) :=
  contDiff_const.mul
    (punctureRadialOrderIso_smooth.comp (contDiff_const.add (contDiff_id.div_const k)))

/-- Positive scaling makes the actual raw upper map strictly increasing. -/
theorem upperEndRaw_strictMono {k : ℝ} (hk : 0 < k) : StrictMono (upperEndRaw k) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left
    (sub_lt_sub_right (punctureRadialOrderIso.symm.strictMono
      ((div_lt_div_iff_of_pos_right hk).mpr hst)) 1) hk

/-- Applying the displayed inverse recovers every original real parameter. -/
theorem upperEndRaw_left_inverse {k : ℝ} (hk : 0 < k) :
    Function.LeftInverse (upperEndRawInverse k) (upperEndRaw k) := by
  intro t
  change k * punctureRadialOrderIso
    (1 + k * (punctureRadialOrderIso.symm (t / k) - 1) / k) = t
  have harg : 1 + k * (punctureRadialOrderIso.symm (t / k) - 1) / k =
      punctureRadialOrderIso.symm (t / k) := by field_simp [hk.ne']; ring
  rw [harg, OrderIso.apply_symm_apply, mul_div_cancel₀ _ hk.ne']

/-- The other displayed composition recovers every target parameter. -/
theorem upperEndRaw_right_inverse {k : ℝ} (hk : 0 < k) :
    Function.LeftInverse (upperEndRaw k) (upperEndRawInverse k) := by
  intro t
  change k * (punctureRadialOrderIso.symm (k * punctureRadialOrderIso (1 + t / k) / k) - 1) = t
  rw [mul_div_cancel_left₀ _ hk.ne', OrderIso.symm_apply_apply]
  field_simp [hk.ne']
  ring

/-- The positive actual derivative follows from monotonicity and the smooth inverse identity. -/
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

/-- The lower bound for the original profile makes its rescaled inverse a contraction in value. -/
theorem upperEndRaw_le_self {k : ℝ} (hk : 0 < k) (t : ℝ) : upperEndRaw k t ≤ t := by
  have h := punctureRadialOrderIso_lower (punctureRadialOrderIso.symm (t / k))
  rw [OrderIso.apply_symm_apply] at h
  have hmul := mul_le_mul_of_nonneg_left h hk.le
  simpa only [upperEndRaw, mul_div_cancel₀ _ hk.ne'] using hmul

/-- Negative parameters retain the exact identity formula. -/
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

/-- The upper cutoff increases from zero to one between one eighth and one quarter. -/
noncomputable def upperEndCutoff (t : ℝ) : ℝ := Real.smoothTransition (8 * t - 1)

/-- The final scalar change retains the raw upper formula before becoming identity. -/
noncomputable def upperEndProfile (k t : ℝ) : ℝ :=
  (1 - upperEndCutoff t) * upperEndRaw k t + upperEndCutoff t * t

/-- The cutoff is smooth on the actual full line. -/
theorem upperEndCutoff_smooth : ContDiff ℝ ∞ upperEndCutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The cutoff is monotone, so its derivative is nonnegative. -/
theorem upperEndCutoff_monotone : Monotone upperEndCutoff := by
  intro s t hst
  exact Real.smoothTransition.monotone (by linarith)

/-- The raw inverse formula is exact throughout the entire inner interval. -/
theorem upperEndProfile_inner (k : ℝ) {t : ℝ} (ht : t ≤ 1 / 8) :
    upperEndProfile k t = upperEndRaw k t := by
  have hq : upperEndCutoff t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [upperEndProfile, hq]
  ring

/-- The same scalar map is identity from one quarter onward. -/
theorem upperEndProfile_outer (k : ℝ) {t : ℝ} (ht : 1 / 4 ≤ t) :
    upperEndProfile k t = t := by
  have hq : upperEndCutoff t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  rw [upperEndProfile, hq]
  ring

/-- The negative half-line also remains pointwise fixed. -/
theorem upperEndProfile_nonpos {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : t ≤ 0) :
    upperEndProfile k t = t := by
  rw [upperEndProfile_inner k (by linarith), upperEndRaw_nonpos hk ht]

/-- The original blended profile is globally smooth. -/
theorem upperEndProfile_smooth (k : ℝ) : ContDiff ℝ ∞ (upperEndProfile k) :=
  ((contDiff_const.sub upperEndCutoff_smooth).mul (upperEndRaw_smooth k)).add
    (upperEndCutoff_smooth.mul contDiff_id)

/-- The actual derivative separates its convex slopes and nonnegative cutoff correction. -/
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

/-- Every positive scale makes the derivative of the same blended profile strictly positive. -/
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

/-- The actual scalar change is strictly increasing on the whole line. -/
theorem upperEndProfile_strictMono {k : ℝ} (hk : 0 < k) : StrictMono (upperEndProfile k) :=
  strictMono_of_deriv_pos (upperEndProfile_deriv_pos hk)

/-- Exterior identity gives a preimage for every real target by the intermediate value theorem. -/
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

/-- The actual upper profile as a global real order isomorphism. -/
noncomputable def upperEndOrderIso (k : ℝ) (hk : 0 < k) : ℝ ≃o ℝ :=
  (upperEndProfile_strictMono hk).orderIsoOfSurjective _ (upperEndProfile_surjective hk)

/-- The order isomorphism keeps exactly the original total scalar map. -/
@[simp] theorem upperEndOrderIso_apply (k : ℝ) (hk : 0 < k) (t : ℝ) :
    upperEndOrderIso k hk t = upperEndProfile k t := rfl

/-- The actual inverse is globally smooth because this actual derivative never vanishes. -/
theorem upperEndOrderIso_symm_smooth {k : ℝ} (hk : 0 < k) :
    ContDiff ℝ ∞ (upperEndOrderIso k hk).symm := by
  apply (upperEndOrderIso k hk).toHomeomorph.contDiff_symm_deriv
    (fun t => (upperEndProfile_deriv_pos hk t).ne')
    (fun t => ((upperEndProfile_smooth k).differentiable (by simp) t).hasDerivAt)
    (upperEndProfile_smooth k)

/-- The actual lower endpoint is fixed. -/
@[simp] theorem upperEndOrderIso_zero (k : ℝ) (hk : 0 < k) : upperEndOrderIso k hk 0 = 0 :=
  upperEndProfile_nonpos hk le_rfl

/-- The actual upper endpoint remains in the exterior identity region. -/
@[simp] theorem upperEndOrderIso_one (k : ℝ) (hk : 0 < k) : upperEndOrderIso k hk 1 = 1 :=
  upperEndProfile_outer k (by norm_num)

end PoincareMT.M38
