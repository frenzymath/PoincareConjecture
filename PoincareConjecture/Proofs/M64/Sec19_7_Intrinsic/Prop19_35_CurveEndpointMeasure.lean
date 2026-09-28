import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointMeasure











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem m64Intrinsic_curve_lift_speed_le
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {gamma target : ℝ → AnnulusCoordinates} {s c : ℝ}
    (he : DifferentiableAt ℝ e (gamma s)) (hg : DifferentiableAt ℝ gamma s)
    (hlift : (e ∘ gamma) =ᶠ[𝓝 s] target)
    (hbound : ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 (gamma s 0) ^ 2 * (v 0) ^ 2 +
        (v 1) ^ 2) ≤ N.metric.inner (e (gamma s))
          (fderiv ℝ e (gamma s) v) (fderiv ℝ e (gamma s) v)) :
    c * intrinsicBoundarySpeed N.metric 1 (gamma s 0) * |deriv gamma s 0| ≤
      Real.sqrt (N.metric.inner (target s) (deriv target s) (deriv target s)) := by
  have hchain : HasDerivAt (e ∘ gamma) (fderiv ℝ e (gamma s) (deriv gamma s)) s :=
    he.hasFDerivAt.comp_hasDerivAt s hg.hasDerivAt
  have hd : fderiv ℝ e (gamma s) (deriv gamma s) = deriv target s :=
    (hchain.congr_of_eventuallyEq hlift.symm).deriv.symm
  have hpoint : e (gamma s) = target s := hlift.self_of_nhds
  have h := hbound (deriv gamma s)
  rw [hd, hpoint] at h
  apply Real.le_sqrt_of_sq_le
  have hdiscard : 0 ≤ c ^ 2 * (deriv gamma s 1) ^ 2 :=
    mul_nonneg (sq_nonneg c) (sq_nonneg _)
  rw [mul_pow, mul_pow, sq_abs]
  nlinarith only [h, hdiscard]




theorem m64Intrinsic_lifted_curve_measure_le
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {gamma target : ℝ → AnnulusCoordinates}
    {J B : Set ℝ} (hJ : IsOpen J) (hg : ContDiffOn ℝ ∞ gamma J)
    (he : ∀ s ∈ J, DifferentiableAt ℝ e (gamma s))
    (hlift : ∀ s ∈ J, e (gamma s) = target s)
    (hB : MeasurableSet B) (hBJ : B ⊆ J)
    (hinj : InjOn (fun s => gamma s 0) B) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ s ∈ B, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 (gamma s 0) ^ 2 * (v 0) ^ 2 +
        (v 1) ^ 2) ≤ N.metric.inner (e (gamma s))
          (fderiv ℝ e (gamma s) v) (fderiv ℝ e (gamma s) v)) :
    ENNReal.ofReal c *
        (∫⁻ a in (fun s => gamma s 0) '' B,
          ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
      ∫⁻ s in B, ENNReal.ofReal
        (Real.sqrt (N.metric.inner (target s) (deriv target s) (deriv target s))) := by
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
  have hspeed := m64Intrinsic_curve_lift_speed_le N (he s (hBJ hs))
    ((hga s hs).differentiableAt (by simp)) (target := target)
    (c := c) (hbound := hbound s hs) (by
      filter_upwards [hJ.mem_nhds (hBJ hs)] with x hx
      exact hlift x hx)
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  convert hspeed using 1
  dsimp only [f, f']
  ring



theorem m64Intrinsic_lifted_curve_endpoint_graph_measure_le
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {gamma target : ℝ → AnnulusCoordinates}
    {J B T : Set ℝ} (hJ : IsOpen J) (hg : ContDiffOn ℝ ∞ gamma J)
    (he : ∀ s ∈ J, DifferentiableAt ℝ e (gamma s))
    (hlift : ∀ s ∈ J, e (gamma s) = target s)
    (hB : MeasurableSet B) (hBJ : B ⊆ J) (hBT : B ⊆ T)
    (htargetInj : InjOn target T)
    {height : ℝ → ℝ} (hgraph : ∀ s ∈ B, gamma s 1 = height (gamma s 0))
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ s ∈ B, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 (gamma s 0) ^ 2 * (v 0) ^ 2 +
        (v 1) ^ 2) ≤ N.metric.inner (e (gamma s))
          (fderiv ℝ e (gamma s) v) (fderiv ℝ e (gamma s) v)) :
    ENNReal.ofReal c *
        (∫⁻ a in (fun s => gamma s 0) '' B,
          ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
      ∫⁻ s in B, ENNReal.ofReal
        (Real.sqrt (N.metric.inner (target s) (deriv target s) (deriv target s))) := by
  apply m64Intrinsic_lifted_curve_measure_le N hJ hg he hlift hB hBJ ?_ hc hbound
  intro x hx y hy hxy
  change gamma x 0 = gamma y 0 at hxy
  have hgamma : gamma x = gamma y := by
    ext i
    fin_cases i
    · exact hxy
    · change gamma x 1 = gamma y 1
      rw [hgraph x hx, hgraph y hy, hxy]
  apply htargetInj (hBT hx) (hBT hy)
  rw [← hlift x (hBJ hx), ← hlift y (hBJ hy), hgamma]

end PoincareConjecture
