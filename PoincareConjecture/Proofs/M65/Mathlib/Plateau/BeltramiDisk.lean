import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiReflectionEquation
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology ContDiff ComplexConjugate SchwartzMap

namespace Complex

private theorem inversion_eq_self_iff {z : ℂ} (hz : z ≠ 0) :
    beltramiCircleInversion z = z ↔ ‖z‖ = 1 := by
  constructor
  · intro h
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hh := congrArg norm h
    simp only [beltramiCircleInversion, norm_inv, norm_conj] at hh
    have hp : ‖z‖ * ‖z‖ = 1 := by
      calc
        _ = ‖z‖ * ‖z‖⁻¹ := congrArg (fun t : ℝ => ‖z‖ * t) hh.symm
        _ = 1 := mul_inv_cancel₀ hn
    nlinarith [norm_nonneg z]
  · intro h
    apply inv_eq_of_mul_eq_one_left
    rw [mul_conj', h]
    norm_num

private theorem sphere_invariant (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0)
    (hJ : ∀ z, f (beltramiCircleInversion z) = beltramiCircleInversion (f z)) (z : ℂ) :
    ‖f z‖ = 1 ↔ ‖z‖ = 1 := by
  by_cases hz : z = 0
  · simp only [hz, hf0, norm_zero, zero_ne_one]
  · have hfz : f z ≠ 0 := by
      intro h
      exact hz (f.injective (h.trans hf0.symm))
    rw [← inversion_eq_self_iff hfz, ← hJ, f.injective.eq_iff,
      inversion_eq_self_iff hz]

private theorem closed_disk_forward (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0)
    (hs : ∀ z, ‖f z‖ = 1 ↔ ‖z‖ = 1) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖f z‖ ≤ 1 := by
  by_contra hh
  have hgt : 1 < ‖f z‖ := lt_of_not_ge hh
  let q : ℝ → ℝ := fun t => ‖f (t • z)‖
  have hq : Continuous q := f.continuous.comp (continuous_id.smul continuous_const) |>.norm
  have hq0 : q 0 = 0 := by simp only [q, zero_smul, hf0, norm_zero]
  have hq1 : q 1 = ‖f z‖ := by simp only [q, one_smul]
  obtain ⟨t, ht, hqt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hq.continuousOn (show (1 : ℝ) ∈ Icc (q 0) (q 1) by rw [hq0, hq1]; exact ⟨by norm_num, hgt.le⟩)
  have htn : t ≠ 1 := by
    intro he
    subst t
    rw [hq1] at hqt
    exact (ne_of_gt hgt) hqt
  have htnorm : ‖t • z‖ = 1 := (hs _).mp hqt
  have hsmall : ‖t • z‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left hz ht.1
      _ < 1 := by simpa only [mul_one] using lt_of_le_of_ne ht.2 htn
  exact (ne_of_lt hsmall) htnorm

theorem exists_disk_smooth_beltrami_diffeomorphism (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : k < 1)
    (hbound : ∀ z, ‖μ z‖ ≤ k) (hzero : ∀ᶠ z in 𝓝 (0 : ℂ), μ z = 0)
    (href : ∀ z ≠ 0, μ z = (z / conj z) ^ 2 * conj (μ (beltramiCircleInversion z))) :
    ∃ f : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (f : ℂ → ℂ) ∧ ContDiff ℝ ∞ (f.symm : ℂ → ℂ) ∧
      f 0 = 0 ∧ f 1 = 1 ∧ (∀ z, ‖f z‖ ≤ 1 ↔ ‖z‖ ≤ 1) ∧
      (∀ z, ‖f z‖ < 1 ↔ ‖z‖ < 1) ∧
      ∀ z, fderiv ℝ (f : ℂ → ℂ) z 1 + I * fderiv ℝ (f : ℂ → ℂ) z I =
        μ z * (fderiv ℝ (f : ℂ → ℂ) z 1 - I * fderiv ℝ (f : ℂ → ℂ) z I) := by
  obtain ⟨f, hf, hfi, hf0, hf1, a, ha, hflim, heq⟩ :=
    exists_normalized_smooth_beltrami_diffeomorphism μ hμ hk hbound
  have hhol0 : AnalyticAt ℂ (f : ℂ → ℂ) 0 := by
    apply analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hzero] with z hz
    apply differentiableAt_complex_of_beltrami_zero (hf.differentiable (by simp) z)
    rw [heq, hz, zero_mul]
  have hfi0 : f.symm 0 = 0 := f.injective (by simpa only [f.apply_symm_apply] using hf0.symm)
  have hder0 : deriv (f : ℂ → ℂ) 0 ≠ 0 := by
    have hh := holomorphic_inverse_of_real_differentiable f (z := 0)
      (show DifferentiableAt ℂ (f : ℂ → ℂ) (f.symm 0) by
        rw [hfi0]; exact hhol0.differentiableAt) (hfi.differentiable (by simp) 0)
    simpa only [hfi0] using hh.1
  let R := beltramiReflectedHomeomorph f hf0
  have hR0 : R 0 = 0 := by
    change beltramiCircleReflect f 0 = 0
    simp only [beltramiCircleReflect,
      beltramiCircleInversion, map_zero, inv_zero, hf0]
  have hR1 : R 1 = 1 := by
    change beltramiCircleReflect f 1 = 1
    simp only [beltramiCircleReflect,
      beltramiCircleInversion, map_one, inv_one, hf1]
  have hR := smooth_beltramiReflectedHomeomorph f hf0 hf hfi μ hμ heq
  have hReq := beltramiReflectedHomeomorph_equation f hf0 hf μ hμ hzero.self_of_nhds heq href
  have hequal : f = R := normalized_smooth_beltrami_unique f R μ hf hfi hR.1
    hf0 hf1 hR0 hR1 ha hflim (fderiv_beltramiCircleReflect_tendsto f hf0 hhol0 hder0)
    heq hReq
  have hJ (z : ℂ) : f (beltramiCircleInversion z) = beltramiCircleInversion (f z) := by
    have hh := congrArg (fun e : ℂ ≃ₜ ℂ => e (beltramiCircleInversion z)) hequal
    change f (beltramiCircleInversion z) =
      beltramiCircleInversion (f (beltramiCircleInversion (beltramiCircleInversion z))) at hh
    simpa only [beltramiCircleInversion_involutive] using hh
  have hs := sphere_invariant f hf0 hJ
  have hclosed (z : ℂ) : ‖f z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by
    constructor
    · intro hz
      have his (y : ℂ) : ‖f.symm y‖ = 1 ↔ ‖y‖ = 1 := by
        simpa only [f.apply_symm_apply] using (hs (f.symm y)).symm
      simpa only [f.symm_apply_apply] using closed_disk_forward f.symm hfi0 his hz
    · exact closed_disk_forward f hf0 hs
  refine ⟨f, hf, hfi, hf0, hf1, hclosed, ?_, heq⟩
  intro z
  exact lt_iff_le_and_ne.trans ((hclosed z).and (not_congr (hs z))) |>.trans
    lt_iff_le_and_ne.symm

end Complex
