import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace PoincareConjecture.Surface

theorem arccos_unit_upper {a b : ℝ} (hunit : a ^ 2 + b ^ 2 = 1) (hb : 0 < b) :
    Real.arccos a ∈ Ioo 0 Real.pi ∧
      Real.cos (Real.arccos a) = a ∧ Real.sin (Real.arccos a) = b := by
  have ha₁ : -1 < a := by nlinarith [sq_pos_of_pos hb]
  have ha₂ : a < 1 := by nlinarith [sq_pos_of_pos hb]
  refine ⟨⟨Real.arccos_pos.mpr ha₂, Real.arccos_lt_pi.mpr ha₁⟩,
    Real.cos_arccos ha₁.le ha₂.le, ?_⟩
  rw [Real.sin_arccos, show 1 - a ^ 2 = b ^ 2 by linarith, Real.sqrt_sq hb.le]

theorem arccos_lt_arccos_of_unit_det_pos {a b c d : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) (hcd : c ^ 2 + d ^ 2 = 1)
    (hb : 0 < b) (hd : 0 < d) (hdet : 0 < a * d - b * c) :
    Real.arccos a < Real.arccos c := by
  obtain ⟨hα, hcα, hsα⟩ := arccos_unit_upper hab hb
  obtain ⟨hβ, hcβ, hsβ⟩ := arccos_unit_upper hcd hd
  have hsin : 0 < Real.sin (Real.arccos c - Real.arccos a) := by
    rw [Real.sin_sub, hcα, hsα, hcβ, hsβ]
    nlinarith
  by_contra h
  have hnonpos := Real.sin_nonpos_of_nonpos_of_neg_pi_le
    (sub_nonpos.mpr (le_of_not_gt h)) (show -Real.pi ≤
      Real.arccos c - Real.arccos a by linarith [hα.2, hβ.1])
  linarith

private theorem contDiffOn_of_exp_eq
    {U : Set ℝ} (hU : IsOpen U) {z w : ℝ → ℂ}
    (hz : ContDiffOn ℝ ∞ z U) (hw : ContinuousOn w U)
    (hexp : ∀ t ∈ U, Complex.exp (w t) = z t) : ContDiffOn ℝ ∞ w U := by
  intro t ht
  have hwt := hw.continuousAt (hU.mem_nhds ht)
  have hz0 : z t ≠ 0 := by rw [← hexp t ht]; exact Complex.exp_ne_zero _
  have hquot : ContDiffAt ℝ ∞ (fun s => z s / z t) t :=
    (hz.contDiffAt (hU.mem_nhds ht)).div_const _
  have hlog : ContDiffAt ℝ ∞ (fun s => Complex.log (z s / z t) + w t) t := by
    apply ContDiffAt.add _ contDiffAt_const
    have hslit : z t / z t ∈ Complex.slitPlane := by
      rw [div_self hz0]
      exact Complex.one_mem_slitPlane
    exact ((Complex.contDiffAt_log (n := ∞) hslit).restrict_scalars ℝ).comp t hquot
  have heq : (fun s => Complex.log (z s / z t) + w t) =ᶠ[𝓝 t] w := by
    have hsmall : ∀ᶠ s in 𝓝 t, (w s - w t).im ∈ Ioo (-Real.pi) Real.pi := by
      apply (Complex.continuous_im.continuousAt.comp (hwt.sub continuousAt_const)).eventually
      change Ioo (-Real.pi) Real.pi ∈ 𝓝 ((w t - w t).im)
      simp only [sub_self, Complex.zero_im]
      exact isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-Real.pi) Real.pi by
        constructor <;> linarith [Real.pi_pos])
    filter_upwards [hU.mem_nhds ht, hsmall] with s hs hsmall
    rw [← hexp s hs, ← hexp t ht, ← Complex.exp_sub,
      Complex.log_exp hsmall.1 hsmall.2.le]
    exact sub_add_cancel _ _
  exact (hlog.congr_of_eventuallyEq heq.symm).contDiffWithinAt

theorem exists_contDiffOn_angle
    {U : Set ℝ} (hU : IsOpen U) (hconv : Convex ℝ U) (hne : U.Nonempty)
    {a b : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hunit : ∀ t ∈ U, (a t) ^ 2 + (b t) ^ 2 = 1) :
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ ∞ θ U ∧
      ∀ t ∈ U, Real.cos (θ t) = a t ∧ Real.sin (θ t) = b t := by
  let z : ℝ → ℂ := fun t => (a t : ℂ) + (b t : ℂ) * Complex.I
  have hz : ContDiffOn ℝ ∞ z U :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn ha).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hb).mul contDiffOn_const)
  have hnorm (t : ℝ) (ht : t ∈ U) : ‖z t‖ = 1 := by
    rw [Complex.norm_def]
    simp [z, Complex.normSq_apply, ← pow_two, hunit t ht]
  have hzero : 0 ∉ z '' U := by
    rintro ⟨t, ht, heq⟩
    have := hnorm t ht
    rw [heq, norm_zero] at this
    norm_num at this
  have hsc : IsSimplyConnected U := by
    let := hconv.contractibleSpace hne
    change SimplyConnectedSpace U
    infer_instance
  obtain ⟨w, hw, hexp⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc hU
    hz.continuousOn hzero
  have hws := contDiffOn_of_exp_eq hU hz hw hexp
  refine ⟨fun t => (w t).im, Complex.imCLM.contDiff.comp_contDiffOn hws, ?_⟩
  intro t ht
  have hre : (w t).re = 0 := by
    have h := congrArg norm (hexp ht)
    dsimp only [Function.comp_apply] at h
    rw [Complex.norm_exp, hnorm t ht, Real.exp_eq_one_iff] at h
    exact h
  have hr := congrArg Complex.re (hexp ht)
  have hi := congrArg Complex.im (hexp ht)
  simpa [Complex.exp_re, Complex.exp_im, hre, z] using And.intro hr hi

theorem exists_contDiffOn_angle_integral
    {U : Set ℝ} (hU : IsOpen U) (hconv : Convex ℝ U) (hne : U.Nonempty)
    {a b : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hunit : ∀ t ∈ U, (a t) ^ 2 + (b t) ^ 2 = 1)
    {s t : ℝ} (hst : uIcc s t ⊆ U) :
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ ∞ θ U ∧
      (∀ x ∈ U, Real.cos (θ x) = a x ∧ Real.sin (θ x) = b x) ∧
      (∫ x in s..t, a x * deriv b x - b x * deriv a x) = θ t - θ s := by
  obtain ⟨θ, hθ, hcoeff⟩ := exists_contDiffOn_angle hU hconv hne ha hb hunit
  refine ⟨θ, hθ, hcoeff, ?_⟩
  have hderiv (x : ℝ) (hx : x ∈ U) :
      a x * deriv b x - b x * deriv a x = deriv θ x := by
    have hd := (hθ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hcos : a =ᶠ[𝓝 x] fun y => Real.cos (θ y) := by
      filter_upwards [hU.mem_nhds hx] with y hy using (hcoeff y hy).1.symm
    have hsin : b =ᶠ[𝓝 x] fun y => Real.sin (θ y) := by
      filter_upwards [hU.mem_nhds hx] with y hy using (hcoeff y hy).2.symm
    rw [hcos.deriv_eq, hsin.deriv_eq, hd.hasDerivAt.cos.deriv, hd.hasDerivAt.sin.deriv,
      ← (hcoeff x hx).1, ← (hcoeff x hx).2]
    calc
      _ = (Real.sin (θ x) ^ 2 + Real.cos (θ x) ^ 2) * deriv θ x := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]
  rw [intervalIntegral.integral_congr (fun x hx => hderiv x (hst hx))]
  apply intervalIntegral.integral_deriv_eq_sub
    (fun x hx => (hθ.contDiffAt (hU.mem_nhds (hst hx))).differentiableAt (by simp))
  exact ((hθ.continuousOn_deriv_of_isOpen hU (by simp)).mono hst).intervalIntegrable

theorem integral_angularForm_eq_int_mul_two_pi
    {U : Set ℝ} (hU : IsOpen U) (hconv : Convex ℝ U) (hne : U.Nonempty)
    {a b : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hunit : ∀ t ∈ U, (a t) ^ 2 + (b t) ^ 2 = 1)
    {s t : ℝ} (hst : uIcc s t ⊆ U) (haeq : a t = a s) (hbeq : b t = b s) :
    ∃ k : ℤ, (∫ x in s..t, a x * deriv b x - b x * deriv a x) =
      2 * Real.pi * k := by
  obtain ⟨θ, _, hcoeff, hint⟩ := exists_contDiffOn_angle_integral hU hconv hne ha hb hunit hst
  have hcos : Real.cos (θ t) = Real.cos (θ s) := by
    rw [(hcoeff t (hst right_mem_uIcc)).1, (hcoeff s (hst left_mem_uIcc)).1, haeq]
  have hsin : Real.sin (θ t) = Real.sin (θ s) := by
    rw [(hcoeff t (hst right_mem_uIcc)).2, (hcoeff s (hst left_mem_uIcc)).2, hbeq]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
    (Real.Angle.cos_sin_inj hcos hsin)
  exact ⟨k, hint.trans hk⟩

end PoincareConjecture.Surface
