import PoincareConjecture.Proofs.M14.Sec6_6_RescalingGeometry
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

theorem rescalingRawIntegrand (γ : ℝ → G.Point) (v : ∀ t, G.Horizontal (γ t)) (t : ℝ) :
    M14RawLIntegrand (rescalingTransport hM12 hM13 G Q hQ a)
      (fun s => γ (s / Q))
      (fun s => Q⁻¹ • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
        (γ (s / Q)) (v (s / Q))) t =
      (Real.sqrt Q / Q) * M14RawLIntegrand G γ v (t / Q) := by
  unfold M14RawLIntegrand
  rw [rescalingTransport_scalar]
  change Real.sqrt t * (Q⁻¹ * horizontalScalarCurvature G.leafwise (γ (t / Q)) +
    (M13.parabolicSpacetime G.spacetime Q hQ a).horizontalMetric.inner (γ (t / Q))
      (Q⁻¹ • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ (t / Q)) (v (t / Q)))
      (Q⁻¹ • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (γ (t / Q)) (v (t / Q)))) = _
  simp only [map_smul, smul_apply, smul_eq_mul, M13.parabolicSpacetime_metric]
  have hs : Real.sqrt t = Real.sqrt Q * Real.sqrt (t / Q) := by
    rw [← Real.sqrt_mul hQ.le, mul_div_cancel₀ _ hQ.ne']
  rw [hs]
  field_simp [hQ.ne']

theorem rescalingRawIntegrand_integrable
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y) :
    IntervalIntegrable
      (M14RawLIntegrand (rescalingTransport hM12 hM13 G Q hQ a)
        (fun s => p.curve (s / Q))
        (fun s => Q⁻¹ • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
          (p.curve (s / Q)) (p.horizontal_velocity (s / Q))))
      MeasureTheory.volume (Q * τ₁) (Q * τ₂) := by
  have h := (p.action_integrable.comp_mul_right (c := Q⁻¹)).const_mul (Real.sqrt Q / Q)
  have heq : M14RawLIntegrand (rescalingTransport hM12 hM13 G Q hQ a)
      (fun s => p.curve (s / Q))
      (fun s => Q⁻¹ • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
        (p.curve (s / Q)) (p.horizontal_velocity (s / Q))) =
      (fun s => (Real.sqrt Q / Q) * M14RawLIntegrand G p.curve p.horizontal_velocity (s / Q)) :=
    funext (rescalingRawIntegrand hM12 hM13 G Q hQ a p.curve p.horizontal_velocity)
  rw [heq]
  simpa only [div_eq_mul_inv, inv_inv, mul_comm τ₁ Q, mul_comm τ₂ Q] using h

noncomputable def rescalingPath
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y := by
  have hmap : MapsTo (fun s : ℝ => s / Q) (Icc (Q * τ₁) (Q * τ₂)) (Icc τ₁ τ₂) := by
    intro s hs
    exact ⟨(le_div_iff₀ hQ).mpr (by simpa only [mul_comm] using hs.1),
      (div_le_iff₀ hQ).mpr (by simpa only [mul_comm] using hs.2)⟩
  have hmapo : MapsTo (fun s : ℝ => s / Q) (Ioo (Q * τ₁) (Q * τ₂)) (Ioo τ₁ τ₂) := by
    intro s hs
    exact ⟨(lt_div_iff₀ hQ).mpr (by simpa only [mul_comm] using hs.1),
      (div_lt_iff₀ hQ).mpr (by simpa only [mul_comm] using hs.2)⟩
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s / Q) :=
    (contDiff_id.div_const Q).contMDiff
  refine {
    tau_nonneg := mul_nonneg hQ.le p.tau_nonneg
    tau_lt := mul_lt_mul_of_pos_left p.tau_lt hQ
    base_time := ?_
    endpoint_time := ?_
    curve := fun s => p.curve (s / Q)
    curve_start := by simpa only [mul_div_cancel_left₀ _ hQ.ne'] using p.curve_start
    curve_end := by simpa only [mul_div_cancel_left₀ _ hQ.ne'] using p.curve_end
    curve_time := ?_
    curve_continuous := p.curve_continuous.comp hc.continuous.continuousOn hmap
    curve_regular := p.curve_regular.comp (hc.of_le (by simp)).contMDiffOn hmapo
    horizontal_velocity := fun s => Q⁻¹ •
      M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (p.curve (s / Q))
        (p.horizontal_velocity (s / Q))
    derivative_eq := ?_
    action_integrable := rescalingRawIntegrand_integrable hM12 hM13 G Q hQ a p }
  · change parabolicTime Q a (G.spacetime.timeFunction x) = _
    rw [p.base_time]
    unfold parabolicTime
    ring
  · change parabolicTime Q a (G.spacetime.timeFunction y) = _
    rw [p.endpoint_time]
    unfold parabolicTime
    ring
  · intro s hs
    change parabolicTime Q a (G.spacetime.timeFunction (p.curve (s / Q))) = _
    rw [p.curve_time _ (hmap hs)]
    unfold parabolicTime
    field_simp [hQ.ne']
    ring
  · intro s hs
    have hp := (p.curve_regular.contMDiffAt (isOpen_Ioo.mem_nhds (hmapo hs))).mdifferentiableAt
      (by simp)
    have hd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r / Q) s
        (ContinuousLinearMap.toSpanSingleton ℝ (Q⁻¹ : ℝ)) := by
      simpa only [id_eq, one_div] using
        ((hasDerivAt_id s).div_const Q).hasFDerivAt.hasMFDerivAt
    change mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) (p.curve ∘ (fun r => r / Q)) s 1 = _
    rw [mfderiv_comp s hp hd.mdifferentiableAt, hd.mfderiv]
    erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply_one]
    change mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) p.curve (s / Q) (Q⁻¹ : ℝ) = _
    have hscaled : mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) p.curve (s / Q) (Q⁻¹ : ℝ) =
        Q⁻¹ • mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) p.curve (s / Q) (1 : ℝ) := by
      simpa only [smul_eq_mul, mul_one] using
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) p.curve (s / Q)).map_smul (Q⁻¹ : ℝ) (1 : ℝ)
    rw [hscaled, p.derivative_eq _ (hmapo hs)]
    change Q⁻¹ • (-G.spacetime.timeVector (p.curve (s / Q)) +
      (p.horizontal_velocity (s / Q)).val) =
      -((1 / Q : ℝ) • G.spacetime.timeVector (p.curve (s / Q))) +
        Q⁻¹ • (p.horizontal_velocity (s / Q)).val
    simp only [smul_add, smul_neg, one_div]

theorem rescalingPath_curve
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y) (s : ℝ) :
    (rescalingPath hM12 hM13 G Q hQ a p).curve (Q * s) = p.curve s := by
  change p.curve (Q * s / Q) = p.curve s
  rw [mul_div_cancel_left₀ _ hQ.ne']

theorem rescalingPath_action
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14BackwardLAction (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p) = Real.sqrt Q * M14BackwardLAction G p := by
  change (∫ s in Q * τ₁..Q * τ₂,
    M14RawLIntegrand (rescalingTransport hM12 hM13 G Q hQ a)
      (fun s => p.curve (s / Q))
      (fun s => Q⁻¹ • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
        (p.curve (s / Q)) (p.horizontal_velocity (s / Q))) s) = _
  simp_rw [rescalingRawIntegrand]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div _ hQ.ne', mul_div_cancel_left₀ _ hQ.ne',
    mul_div_cancel_left₀ _ hQ.ne']
  change (Real.sqrt Q / Q) * (Q * M14BackwardLAction G p) = _
  field_simp

end PoincareConjecture.M14
