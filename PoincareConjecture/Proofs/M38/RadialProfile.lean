import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M38

noncomputable def capRadialProfile (r c t : ℝ) : ℝ :=
  c * t + (r - c) * Real.smoothTransition (4 * t - 1)

theorem capRadialProfile_smooth (r c : ℝ) : ContDiff ℝ ∞ (capRadialProfile r c) := by
  unfold capRadialProfile
  exact (contDiff_const.mul contDiff_id).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)))

theorem capRadialProfile_linear (r c t : ℝ) (ht : t ≤ 1 / 4) :
    capRadialProfile r c t = c * t := by
  simp [capRadialProfile, Real.smoothTransition.zero_of_nonpos (by linarith :
    4 * t - 1 ≤ 0)]

theorem capRadialProfile_affine (r c t : ℝ) (ht : 1 / 2 ≤ t) :
    capRadialProfile r c t = r + c * (t - 1) := by
  rw [capRadialProfile, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

@[simp] theorem capRadialProfile_zero (r c : ℝ) : capRadialProfile r c 0 = 0 := by
  rw [capRadialProfile_linear r c 0 (by norm_num), mul_zero]

@[simp] theorem capRadialProfile_one (r c : ℝ) : capRadialProfile r c 1 = r := by
  rw [capRadialProfile_affine r c 1 (by norm_num)]
  ring

theorem capRadialProfile_strictMono {r c : ℝ} (hc : 0 < c) (hcr : c < r) :
    StrictMono (capRadialProfile r c) := by
  intro a b hab
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hab hc)
    (mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone (by linarith))
      (sub_nonneg.mpr hcr.le))

theorem capRadialProfile_deriv_pos {r c : ℝ} (hc : 0 < c) (hcr : c < r) (t : ℝ) :
    0 < deriv (capRadialProfile r c) t := by
  let q : ℝ → ℝ := fun s => Real.smoothTransition (4 * s - 1)
  have hq : ContDiff ℝ ∞ q := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hmono : Monotone q := fun a b hab => Real.smoothTransition.monotone (by linarith)
  have hd := ((hasDerivAt_id t).const_mul c).add
    (((hq.differentiable (by simp)) t).hasDerivAt.const_mul (r - c))
  have hderiv : deriv (capRadialProfile r c) t = c + (r - c) * deriv q t := by
    convert hd.deriv using 1 <;> first | rfl | simp only [mul_one]
  rw [hderiv]
  exact add_pos_of_pos_of_nonneg hc
    (mul_nonneg (sub_nonneg.mpr hcr.le) hmono.deriv_nonneg)

theorem capRadialProfile_surjective {r c : ℝ} (hc : 0 < c) (hcr : c < r) :
    Function.Surjective (capRadialProfile r c) := by
  intro y
  have hab : (y - (r - c)) / c ≤ y / c :=
    (div_le_div_iff_of_pos_right hc).mpr (by linarith)
  have hlo : capRadialProfile r c ((y - (r - c)) / c) ≤ y := by
    have h := mul_le_mul_of_nonneg_left
      (Real.smoothTransition.le_one (4 * ((y - (r - c)) / c) - 1))
      (sub_nonneg.mpr hcr.le)
    dsimp [capRadialProfile]
    rw [mul_div_cancel₀ _ hc.ne']
    linarith
  have hhi : y ≤ capRadialProfile r c (y / c) := by
    have h := mul_nonneg (sub_nonneg.mpr hcr.le)
      (Real.smoothTransition.nonneg (4 * (y / c) - 1))
    dsimp [capRadialProfile]
    rw [mul_div_cancel₀ _ hc.ne']
    linarith
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hab
    (capRadialProfile_smooth r c).continuous.continuousOn ⟨hlo, hhi⟩
  exact ⟨t, ht⟩

noncomputable def capRadialOrderIso (r c : ℝ) (hc : 0 < c) (hcr : c < r) : ℝ ≃o ℝ :=
  (capRadialProfile_strictMono hc hcr).orderIsoOfSurjective _
    (capRadialProfile_surjective hc hcr)

@[simp] theorem capRadialOrderIso_apply (r c : ℝ) (hc : 0 < c) (hcr : c < r) (t : ℝ) :
    capRadialOrderIso r c hc hcr t = capRadialProfile r c t := rfl

theorem capRadialOrderIso_symm_smooth {r c : ℝ} (hc : 0 < c) (hcr : c < r) :
    ContDiff ℝ ∞ (capRadialOrderIso r c hc hcr).symm := by
  apply (capRadialOrderIso r c hc hcr).toHomeomorph.contDiff_symm_deriv
    (fun t => (capRadialProfile_deriv_pos hc hcr t).ne')
    (fun t => ((capRadialProfile_smooth r c).differentiable (by simp) t).hasDerivAt)
    (capRadialProfile_smooth r c)

theorem capRadialOrderIso_symm_linear {r c : ℝ} (hc : 0 < c) (hcr : c < r)
    (t : ℝ) (ht : t ≤ c / 4) :
    (capRadialOrderIso r c hc hcr).symm t = t / c := by
  apply (capRadialOrderIso r c hc hcr).injective
  rw [OrderIso.apply_symm_apply, capRadialOrderIso_apply,
    capRadialProfile_linear r c (t / c) ((div_le_iff₀ hc).mpr (by linarith))]
  exact (mul_div_cancel₀ t hc.ne').symm

end PoincareConjecture.M38
