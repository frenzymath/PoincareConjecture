import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointLift
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryParameters
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Complex.Circle














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_boundary_injOn_period {radius : ℝ} (hradius : radius ≠ 0) :
    InjOn (intrinsicAnnulusBoundary radius) (Ico (0 : ℝ) rampPeriod) := by
  intro x hx y hy hxy
  apply Circle.exp_injOn_Ico (by simp only [sub_zero]; exact le_rfl) hx hy
  apply Subtype.ext
  apply Complex.ext
  · have h := congrArg (fun z : AnnulusCoordinates => z 0) hxy
    change radius * Real.cos x = radius * Real.cos y at h
    have hc := mul_left_cancel₀ hradius h
    simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using hc
  · have h := congrArg (fun z : AnnulusCoordinates => z 1) hxy
    change radius * Real.sin x = radius * Real.sin y at h
    have hs := mul_left_cancel₀ hradius h
    simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] using hs




theorem m64Intrinsic_lifted_boundary_measure_le
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {gamma : ℝ → AnnulusCoordinates}
    {J B : Set ℝ} (hJ : IsOpen J) (hg : ContDiffOn ℝ ∞ gamma J)
    (he : ∀ s ∈ J, DifferentiableAt ℝ e (gamma s))
    (hlift : ∀ s ∈ J, e (gamma s) = intrinsicAnnulusBoundary 2 s)
    (hB : MeasurableSet B) (hBJ : B ⊆ J)
    (hinj : InjOn (fun s => gamma s 0) B) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ s ∈ B, ∀ v : AnnulusCoordinates,
      c ^ 2 * ((intrinsicBoundarySpeed N.metric 1 (gamma s 0)) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e (gamma s)) (fderiv ℝ e (gamma s) v) (fderiv ℝ e (gamma s) v)) :
    ENNReal.ofReal c *
        (∫⁻ a in (fun s => gamma s 0) '' B, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
      ∫⁻ s in B, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 2 s) := by
  let f : ℝ → ℝ := fun s => gamma s 0
  let f' : ℝ → ℝ := fun s => deriv gamma s 0
  have hga (s : ℝ) (hs : s ∈ B) : ContDiffAt ℝ ∞ gamma s :=
    hg.contDiffAt (hJ.mem_nhds (hBJ hs))
  have hdf (s : ℝ) (hs : s ∈ B) : HasDerivAt f (f' s) s :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (gamma s) 0).comp_hasDerivAt s
      ((hga s hs).differentiableAt (by simp)).hasDerivAt
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul hB
    (fun s hs => (hdf s hs).hasDerivWithinAt) hinj
    (fun a => ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a))
  rw [hchange, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hB
  intro s hs
  have hspeed := m64Intrinsic_boundary_lift_speed_le N (he s (hBJ hs))
    ((hga s hs).differentiableAt (by simp)) (c := c) (hbound := hbound s hs) ?_
  · rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hc]
    apply ENNReal.ofReal_le_ofReal
    convert hspeed using 1
    dsimp only [f, f']
    ring
  · filter_upwards [hJ.mem_nhds (hBJ hs)] with x hx
    exact hlift x hx





theorem m64Intrinsic_lifted_endpoint_graph_measure_le
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {gamma : ℝ → AnnulusCoordinates}
    {J B : Set ℝ} (hJ : IsOpen J) (hg : ContDiffOn ℝ ∞ gamma J)
    (he : ∀ s ∈ J, DifferentiableAt ℝ e (gamma s))
    (hlift : ∀ s ∈ J, e (gamma s) = intrinsicAnnulusBoundary 2 s)
    (hB : MeasurableSet B) (hBJ : B ⊆ J) (hBP : B ⊆ Ico (0 : ℝ) rampPeriod)
    {height : ℝ → ℝ} (hgraph : ∀ s ∈ B, gamma s 1 = height (gamma s 0))
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ s ∈ B, ∀ v : AnnulusCoordinates,
      c ^ 2 * ((intrinsicBoundarySpeed N.metric 1 (gamma s 0)) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e (gamma s)) (fderiv ℝ e (gamma s) v) (fderiv ℝ e (gamma s) v)) :
    ENNReal.ofReal c *
        (∫⁻ a in (fun s => gamma s 0) '' B, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
      ∫⁻ s in B, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 2 s) := by
  apply m64Intrinsic_lifted_boundary_measure_le N hJ hg he hlift hB hBJ ?_ hc hbound
  intro x hx y hy hxy
  change gamma x 0 = gamma y 0 at hxy
  have hgamma : gamma x = gamma y := by
    ext i
    fin_cases i
    · exact hxy
    · change gamma x 1 = gamma y 1
      rw [hgraph x hx, hgraph y hy, hxy]
  apply m64Intrinsic_boundary_injOn_period (by norm_num : (2 : ℝ) ≠ 0) (hBP hx) (hBP hy)
  rw [← hlift x (hBJ hx), ← hlift y (hBJ hy), hgamma]

end PoincareConjecture
