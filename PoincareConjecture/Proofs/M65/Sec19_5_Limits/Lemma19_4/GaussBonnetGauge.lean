import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeRegularity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch




theorem cauchyGauge_weak_derivatives_projection {B : Type*} [NormedRing B]
    [NormedAlgebra ℂ B] [CompleteSpace B] [NormOneClass B]
    {A : ℂ → B} {R B0 : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2)
    (L : B →L[ℂ] ℂ) :
    ∃ d0 d1 : Lp ℂ 2 (volume : Measure ℂ),
      ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ z, φ z * d0 z) = -∫ z, fderiv ℝ φ z 1 * L (cauchyGauge A z) ∧
        (∫ z, φ z * d1 z) = -∫ z, fderiv ℝ φ z I * L (cauchyGauge A z) := by
  have hP := cauchyGauge_measurable_spec hR hB hA hs hb hsmall
  have hPb (z : ℂ) : ‖cauchyGauge A z‖ ≤ 2 := by
    have hh := norm_le_norm_sub_add (cauchyGauge A z) (1 : B)
    rw [norm_one] at hh
    linarith [hP.2.2.1 z]
  let G (z : ℂ) := A z * cauchyGauge A z
  have hG : AEStronglyMeasurable G volume := hA.mul hP.1.aestronglyMeasurable
  have hGs : Function.support G ⊆ closedBall (0 : ℂ) R :=
    (Function.support_mul_subset_left _ _).trans hs
  have hGb (z : ℂ) : ‖G z‖ ≤ B0 * 2 :=
    (norm_mul_le _ _).trans (mul_le_mul (hb z) (hPb z) (norm_nonneg _) hB)
  let h (z : ℂ) := L (G z)
  have hh : AEStronglyMeasurable h volume := L.continuous.comp_aestronglyMeasurable hG
  have hhs : Function.support h ⊆ closedBall (0 : ℂ) R :=
    (Function.support_comp_subset (map_zero L) G).trans hGs
  have hhb (z : ℂ) : ‖h z‖ ≤ ‖L‖ * (B0 * 2) :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hGb z) (norm_nonneg L))
  have hhL2 : MemLp h 2 volume := memLp_of_bound_support hh hhs hhb 2
  let u := hhL2.toLp h
  have heq (z : ℂ) : L (cauchyGauge A z) = L 1 + cauchyOperator h z := by
    rw [hP.2.1 z, map_add, map_cauchyOperator_of_bound L hG hGs hGb]
  refine ⟨u + beurlingL2 u, I • (beurlingL2 u - u), ?_⟩
  intro φ hφ hφs
  have hw := cauchyOperator_weak_derivatives_C1 hR (by positivity) hhL2 hhs hhb φ hφ hφs
  have hright (v : ℂ) : (∫ z, fderiv ℝ φ z v * L (cauchyGauge A z)) =
      ∫ z, fderiv ℝ φ z v * cauchyOperator h z := by
    have hc : Continuous (fun z => fderiv ℝ φ z v) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs : HasCompactSupport (fun z => fderiv ℝ φ z v) := hφs.fderiv_apply ℝ v
    have hz : (∫ z, fderiv ℝ φ z v) = 0 := by
      have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := volume) (f := φ) (g := fun _ : ℂ => (1 : ℂ)) (v := v)
        (by simpa only [mul_one] using hc.integrable_of_hasCompactSupport hcs)
        (by simp)
        (by simpa only [mul_one] using hφ.continuous.integrable_of_hasCompactSupport hφs)
        (fun z _ => hφ.differentiable one_ne_zero z) (fun _ _ => differentiableAt_const _)
      simpa only [fderiv_const_apply, zero_apply, mul_zero, integral_zero, mul_one,
        eq_neg_iff_add_eq_zero, zero_add] using h
    have hi0 : Integrable (fun z => fderiv ℝ φ z v * L 1) :=
      (hc.integrable_of_hasCompactSupport hcs).mul_const _
    have hCh : Continuous (cauchyOperator h) :=
      continuous_cauchyOperator_of_bound (by positivity) hh hhs hhb
    have hi1 : Integrable (fun z => fderiv ℝ φ z v * cauchyOperator h z) :=
      (hc.mul hCh).integrable_of_hasCompactSupport hcs.mul_right
    simp_rw [heq, mul_add]
    rw [integral_add hi0 hi1, integral_mul_const, hz, zero_mul, zero_add]
  exact ⟨(hright 1).symm ▸ hw.1, (hright I).symm ▸ hw.2⟩

private theorem actual_derivative_eq_L2_of_weak_identity {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) (hFc : Continuous F)
    (v : ℂ) (d : Lp ℂ 2 (volume : Measure ℂ))
    (hweak : ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ z, φ z * d z) = -∫ z, fderiv ℝ φ z v * F z) :
    (fun z => fderiv ℝ F z v) =ᵐ[volume.restrict U] d := by
  have hD : ContinuousOn (fun z => fderiv ℝ F z v) U :=
    (hF.fderiv_of_isOpen (m := 0) hU (by norm_num)).continuousOn.clm_apply continuousOn_const
  have hd : LocallyIntegrable (fun z => d z) volume := (Lp.memLp d).locallyIntegrable (by norm_num)
  have hzero : ∀ᵐ z ∂volume, z ∈ U → fderiv ℝ F z v - d z = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hD.locallyIntegrableOn hU.measurableSet |>.sub (hd.locallyIntegrableOn U))
    intro ψ hψ hψs hψU
    let φ : ℂ → ℂ := fun z => (ψ z : ℂ)
    have hφ : ContDiff ℝ 1 φ := Complex.ofRealCLM.contDiff.comp (hψ.of_le (by simp))
    have hφs : HasCompactSupport φ := hψs.comp_left Complex.ofReal_zero
    have hφU : tsupport φ ⊆ U :=
      (tsupport_comp_subset (map_zero Complex.ofRealCLM) ψ).trans hψU
    have hφD : Continuous (fun z => φ z * fderiv ℝ F z v) :=
      (hφ.continuous.continuousOn.mul hD).continuous_of_tsupport_subset hU
        (tsupport_mul_subset_left.trans hφU)
    have hiD : Integrable (fun z => φ z * fderiv ℝ F z v) :=
      hφD.integrable_of_hasCompactSupport hφs.mul_right
    have hiF : Integrable (fun z => φ z * F z) :=
      (hφ.continuous.mul hFc).integrable_of_hasCompactSupport hφs.mul_right
    have hiφ : Continuous (fun z => fderiv ℝ φ z v * F z) :=
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hFc
    have hiφF : Integrable (fun z => fderiv ℝ φ z v * F z) :=
      hiφ.integrable_of_hasCompactSupport (hφs.fderiv_apply ℝ v).mul_right
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hiφF hiD hiF
      (fun z _ => hφ.differentiable one_ne_zero z)
      (fun z hz => (hF.contDiffAt (hU.mem_nhds (hφU hz))).differentiableAt one_ne_zero)
    have hid : Integrable (fun z => φ z * d z) := by
      simpa only [smul_eq_mul] using hd.integrable_smul_left_of_hasCompactSupport
        hφ.continuous hφs
    calc
      _ = ∫ z, φ z * fderiv ℝ F z v - φ z * d z := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => by
          simp only [φ, Complex.real_smul, Pi.sub_apply, mul_sub]
      _ = 0 := by rw [integral_sub hiD hid, hibp, hweak φ hφ hφs, sub_self]
  filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem hU.measurableSet] with z hz hzU
  exact sub_eq_zero.mp (hz hzU)






theorem cauchyGauge_projection_derivatives_memLp {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {R B0 : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2)
    (hU : IsOpen U) (hAC1 : ContDiffOn ℝ 1 A U)
    (L : ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) →L[ℂ] ℂ) :
    MemLp (fun z => fderiv ℝ (fun w => L (cauchyGauge A w)) z 1)
      2 (volume.restrict U) ∧
    MemLp (fun z => fderiv ℝ (fun w => L (cauchyGauge A w)) z I)
      2 (volume.restrict U) := by
  have hP := cauchyGauge_contDiffOn_of_C1_coefficient hR hB hA hs hb hsmall hU hAC1
  have hPc := (cauchyGauge_measurable_spec hR hB hA hs hb hsmall).1
  have hF : ContDiffOn ℝ 1 (fun z => L (cauchyGauge A z)) U :=
    (L.restrictScalars ℝ).contDiff.comp_contDiffOn hP.1
  have hFc : Continuous (fun z => L (cauchyGauge A z)) := L.continuous.comp hPc
  obtain ⟨d0, d1, hd⟩ := cauchyGauge_weak_derivatives_projection hR hB hA hs hb hsmall L
  have h0 := actual_derivative_eq_L2_of_weak_identity hU hF hFc 1 d0
    (fun φ hφ hφs => (hd φ hφ hφs).1)
  have h1 := actual_derivative_eq_L2_of_weak_identity hU hF hFc I d1
    (fun φ hφ hφs => (hd φ hφ hφs).2)
  exact ⟨((Lp.memLp d0).restrict U).ae_eq h0.symm,
    ((Lp.memLp d1).restrict U).ae_eq h1.symm⟩

end PoincareConjecture.M65Branch
