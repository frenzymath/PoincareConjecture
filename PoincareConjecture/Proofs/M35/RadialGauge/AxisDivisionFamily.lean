import PoincareConjecture.Proofs.M35.RadialGauge.ProfileFamilyPartials
import PoincareConjecture.Proofs.M03.Existence.DeTurckMetricProducerNative
import PoincareConjecture.Proofs.M03.Existence.ImplicitLocalFlowNative











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial ImplicitLocalFlowNative

private noncomputable def profileParameterPath (p : ℝ × ℝ) : C(UnitInterval, ℝ × ℝ) :=
  (ContinuousLinearMap.inl ℝ ℝ ℝ).compLeftContinuous ℝ UnitInterval
    (ContinuousMap.const UnitInterval p.1) +
  (ContinuousLinearMap.inr ℝ ℝ ℝ).compLeftContinuous ℝ UnitInterval
    (p.2 • unitParameter)

private theorem profileParameterPath_apply (p : ℝ × ℝ) (a : UnitInterval) :
    profileParameterPath p a = (p.1, p.2 * a) := by
  simp [profileParameterPath, unitParameter]

private theorem profileParameterPath_contDiff : ContDiff ℝ ∞ profileParameterPath := by
  have hc : ContDiff ℝ ∞ (ContinuousLinearMap.const ℝ UnitInterval : ℝ → Path ℝ) :=
    (ContinuousLinearMap.const ℝ UnitInterval : ℝ →L[ℝ] Path ℝ).contDiff
  exact (((ContinuousLinearMap.inl ℝ ℝ ℝ).compLeftContinuous ℝ UnitInterval).contDiff.comp
    (hc.comp contDiff_fst)).add
    (((ContinuousLinearMap.inr ℝ ℝ ℝ).compLeftContinuous ℝ UnitInterval).contDiff.comp
      (contDiff_snd.smul contDiff_const))



theorem axisDivision_family_contDiffOn {f : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => axisDivision (f p.1) p.2) (J ×ˢ univ) := by
  intro p hp
  let U : Set (ℝ × ℝ) := J ×ˢ univ
  have hU : IsOpen U := hJ.prod isOpen_univ
  let F := Function.uncurry (profileRadiusPartial f)
  have hF : ∀ q ∈ U, ContDiffAt ℝ ∞ F q :=
    fun q hq => (profileRadiusPartial_contDiffOn hJ hf).contDiffAt (hU.mem_nhds hq)
  obtain ⟨eps, heps, Phi, hPhi, hEq⟩ :=
    DeTurckMetricProducerNative.exists_smooth_pointwise_extension hU F hF
      (profileParameterPath p)
      (fun a => by rw [profileParameterPath_apply]; exact ⟨hp.1, mem_univ _⟩)
  let A : Path ℝ →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ unitOne).comp pathIntegralCLM
  have hs : ContDiff ℝ ∞ (fun q : ℝ × ℝ => A (Phi (profileParameterPath q))) :=
    A.contDiff.comp (hPhi.comp profileParameterPath_contDiff)
  apply (hs.contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hclose : ∀ᶠ q in 𝓝 p, ‖profileParameterPath q - profileParameterPath p‖ < eps := by
    have hc : ContinuousAt profileParameterPath p :=
      profileParameterPath_contDiff.continuous.continuousAt
    filter_upwards [hc.tendsto.eventually
      (Metric.ball_mem_nhds (profileParameterPath p) heps)] with q hq
    simpa only [Metric.mem_ball, dist_eq_norm] using hq
  have htime : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 ∈ J :=
    continuous_fst.continuousAt.eventually (hJ.mem_nhds hp.1)
  filter_upwards [hclose, htime] with q hq hqt
  unfold axisDivision CoordinateExponential.radialWeightedIntegral
  change (∫ a in (0 : ℝ)..1, a ^ 0 • deriv (f q.1) (a • q.2)) =
    ∫ a in (0 : ℝ)..1, extendPath (Phi (profileParameterPath q)) a
  apply intervalIntegral.integral_congr
  intro a ha
  have ha' : a ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ha
  let b : UnitInterval := ⟨a, ha'⟩
  change _ = extendPath (Phi (profileParameterPath q)) (b : ℝ)
  rw [extendPath_apply_coe, hEq _ hq b, profileParameterPath_apply]
  change a ^ 0 * deriv (f q.1) (a * q.2) = profileRadiusPartial f q.1 (q.2 * a)
  rw [profileRadiusPartial_eq_deriv hJ hf hqt, pow_zero, one_mul, mul_comm a q.2]

end PoincareConjecture.M35.RadialGauge
