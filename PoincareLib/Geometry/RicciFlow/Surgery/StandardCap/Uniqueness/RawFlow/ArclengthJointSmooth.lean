import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.AxisTimeCoefficients
import PoincareLib.Geometry.RicciFlow.Local.DeTurck.Construction.DeTurckMetricProducer
import PoincareLib.Geometry.RicciFlow.Local.Gauge.Flow.ImplicitLocalFlow

/-!
# Joint smoothness of the actual intrinsic coordinate

Morgan-Tian Section 12.6, pp. 309-313. The compact radial integration
path has a smooth pointwise extension from the actual open time domain.
The lower M03 continuous-path composition and integral operators then
prove joint smoothness of the genuine arclength, in both time and radius.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M35.Uniqueness

open ImplicitLocalFlowNative

private noncomputable def axisParameterPath (p : ℝ × ℝ) : C(UnitInterval, ℝ × ℝ) :=
  (ContinuousLinearMap.inl ℝ ℝ ℝ).compLeftContinuous ℝ UnitInterval
    (ContinuousMap.const UnitInterval p.1) +
  (ContinuousLinearMap.inr ℝ ℝ ℝ).compLeftContinuous ℝ UnitInterval
    (p.2 • unitParameter)

private theorem axisParameterPath_apply (p : ℝ × ℝ) (a : UnitInterval) :
    axisParameterPath p a = (p.1, p.2 * a) := by
  simp [axisParameterPath, unitParameter]

private theorem axisParameterPath_contDiff : ContDiff ℝ ∞ axisParameterPath := by
  have hc : ContDiff ℝ ∞ (ContinuousLinearMap.const ℝ UnitInterval : ℝ → Path ℝ) :=
    (ContinuousLinearMap.const ℝ UnitInterval : ℝ →L[ℝ] Path ℝ).contDiff
  exact (((ContinuousLinearMap.inl ℝ ℝ ℝ).compLeftContinuous ℝ UnitInterval).contDiff.comp
    (hc.comp contDiff_fst)).add
    (((ContinuousLinearMap.inr ℝ ℝ ℝ).compLeftContinuous ℝ UnitInterval).contDiff.comp
      (contDiff_snd.smul contDiff_const))

/-- The actual arclength coordinate is jointly smooth at every interior
raw time, on the entire signed radius axis. -/
theorem raw_radialArclength_contDiffAt {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {p : ℝ × ℝ} (hp : p.1 ∈ Ioo 0 G.lifetime) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => radialArclength (G.flow.metric q.1) q.2) p := by
  let U : Set (ℝ × ℝ) := Ioo 0 G.lifetime ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  let F (q : ℝ × ℝ) := axisRadialSpeed (G.flow.metric q.1) q.2
  have hF : ∀ q ∈ U, ContDiffAt ℝ ∞ F q := by
    intro q hq
    have h := (raw_axisRadialSpeed_contDiffOn G).mono
      (show U ⊆ Ico 0 G.lifetime ×ˢ univ from
        fun _ hz => ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2⟩)
    exact h.contDiffAt (hU.mem_nhds hq)
  obtain ⟨eps, heps, Phi, hPhi, hEq⟩ :=
    DeTurckMetricProducerNative.exists_smooth_pointwise_extension hU F hF
      (axisParameterPath p) (fun a => by rw [axisParameterPath_apply]; exact ⟨hp, mem_univ _⟩)
  let A : Path ℝ →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ unitOne).comp pathIntegralCLM
  have hs : ContDiff ℝ ∞ (fun q : ℝ × ℝ => q.2 * A (Phi (axisParameterPath q))) :=
    contDiff_snd.mul (A.contDiff.comp (hPhi.comp axisParameterPath_contDiff))
  apply hs.contDiffAt.congr_of_eventuallyEq
  have hclose : ∀ᶠ q in 𝓝 p, ‖axisParameterPath q - axisParameterPath p‖ < eps := by
    have hc : ContinuousAt axisParameterPath p := axisParameterPath_contDiff.continuous.continuousAt
    have he : ∀ᶠ y in 𝓝 (axisParameterPath p), y ∈ Metric.ball (axisParameterPath p) eps :=
      Metric.ball_mem_nhds (axisParameterPath p) heps
    filter_upwards [hc.tendsto.eventually he] with q hq
    simpa only [Metric.mem_ball, dist_eq_norm] using hq
  filter_upwards [hclose] with q hq
  have hint : A (Phi (axisParameterPath q)) =
      ∫ a in (0 : ℝ)..1, axisRadialSpeed (G.flow.metric q.1) (q.2 * a) := by
    change (∫ a in (0 : ℝ)..1, extendPath (Phi (axisParameterPath q)) a) = _
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : a ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ha
    let b : UnitInterval := ⟨a, ha'⟩
    change extendPath (Phi (axisParameterPath q)) (b : ℝ) = _
    rw [extendPath_apply_coe, hEq _ hq b, axisParameterPath_apply]
  rw [hint]
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (f := fun a => axisRadialSpeed (G.flow.metric q.1) a) q.2 (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one] at hscale
  exact hscale.symm

theorem raw_radialArclength_contDiffOn {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => radialArclength (G.flow.metric q.1) q.2)
      (Ioo 0 G.lifetime ×ˢ univ) :=
  fun _ hq => (raw_radialArclength_contDiffAt G hq.1).contDiffWithinAt

end PoincareMT.M35.Uniqueness
