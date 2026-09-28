import PoincareConjecture.Proofs.M35.RadialGauge.ForcingExteriorIdentity
import PoincareConjecture.Proofs.M35.RadialGauge.SourceDerivativeDifference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem forcingSpaceDeriv_eq_slice {G : V → ℝ → ℝ} {x : V} {sigma : ℝ}
    (hG : DifferentiableAt ℝ (fun p : V × ℝ => G p.1 p.2) (x, sigma)) :
    forcingSpaceDeriv G x sigma = fderiv ℝ (fun y => G y sigma) x := by
  have hd := hG.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) sigma x))
  have hlin : (ContinuousLinearMap.id ℝ V).prod (0 : V →L[ℝ] ℝ) =
      ContinuousLinearMap.inl ℝ V ℝ := by
    ext v <;> simp
  rw [hlin] at hd
  exact hd.fderiv.symm

private theorem smoothForcing_trace_contDiff {h f₀ xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h)
    (hf : ContDiff ℝ ∞ f₀) (hfo : Function.Odd f₀)
    (hxi : ContDiff ℝ ∞ xi) (hxie : Function.Even xi) (sigma : ℝ) :
    ContDiff ℝ ∞ (fun r : ℝ => smoothGaugeForcing h f₀ xi r sigma) := by
  have hreal : ContDiff ℝ ∞ (fun p : ℝ × ℝ => smoothGaugeForcing h f₀ xi p.1 p.2) :=
    smoothGaugeForcing_contDiff (E := ℝ) (h := h) (f₀ := f₀) (xi := xi)
      hh he hf hfo hxi hxie
  have hgraph : ContDiff ℝ ∞ (fun r : ℝ => (r, sigma)) :=
    contDiff_id.prodMk contDiff_const
  exact ContDiff.comp (g := fun p : ℝ × ℝ => smoothGaugeForcing h f₀ xi p.1 p.2)
    (f := fun r : ℝ => (r, sigma)) hreal hgraph

private theorem smoothForcing_trace_even (h f₀ xi : ℝ → ℝ) (sigma : ℝ) :
    Function.Even (fun r : ℝ => smoothGaugeForcing h f₀ xi r sigma) := by
  intro r
  simp only [smoothGaugeForcing, Real.norm_eq_abs, abs_neg,
    smul_eq_mul, abs_mul, Real.abs_exp]

private theorem smoothForcing_eq_trace_norm (h f₀ xi : ℝ → ℝ) (sigma : ℝ) :
    (fun y : V => smoothGaugeForcing h f₀ xi y sigma) =
      fun y => smoothGaugeForcing h f₀ xi ‖y‖ sigma := by
  funext y
  simp only [smoothGaugeForcing, norm_smul, Real.norm_eq_abs,
    Real.abs_exp, abs_norm, smul_eq_mul, abs_mul]

private theorem norm_even_norm_fderiv {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (he : Function.Even w) (x : V) :
    ‖fderiv ℝ (fun y : V => w ‖y‖) x‖ = |deriv w ‖x‖| := by
  rw [(hasFDerivAt_even_norm hw he x).fderiv, norm_smul,
    Real.norm_eq_abs, innerSL_apply_norm]
  have h := congrArg abs (mul_axisDivision_deriv hw he ‖x‖)
  simpa only [abs_mul, abs_norm, mul_comm] using h

theorem smoothGaugeForcing_space_norm_eq_radial
    {h f₀ xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h) (hzero : h 0 = 0)
    (hf : ContDiff ℝ ∞ f₀) (hfo : Function.Odd f₀)
    (hfzero : f₀ 0 = 0) (hdfzero : deriv f₀ 0 = 1)
    (hxi : ContDiff ℝ ∞ xi) (hxie : Function.Even xi)
    {x : V} (hx : x ≠ 0) (sigma : ℝ) :
    ‖forcingSpaceDeriv (smoothGaugeForcing h f₀ xi) x sigma‖ =
      |deriv (radialGaugeForcing (mapRadius h) f₀ (fun s => s * xi s) sigma) ‖x‖| := by
  let w : ℝ → ℝ := fun r => smoothGaugeForcing h f₀ xi r sigma
  have hws : ContDiff ℝ ∞ w := smoothForcing_trace_contDiff
    (h := h) (f₀ := f₀) (xi := xi) hh he hf hfo hxi hxie sigma
  have hwe : Function.Even w := smoothForcing_trace_even h f₀ xi sigma
  have heq : (fun y : V => smoothGaugeForcing h f₀ xi y sigma) =
      fun y => w ‖y‖ := by
    exact smoothForcing_eq_trace_norm h f₀ xi sigma
  have hG := smoothGaugeForcing_contDiff (E := V) hh he hf hfo hxi hxie
  rw [forcingSpaceDeriv_eq_slice (hG.differentiable (by simp) (x, sigma)), heq,
    norm_even_norm_fderiv hws hwe x]
  have hlocal : w =ᶠ[𝓝 ‖x‖]
      radialGaugeForcing (mapRadius h) f₀ (fun s => s * xi s) sigma := by
    filter_upwards [eventually_gt_nhds (norm_pos_iff.mpr hx)] with r hr
    exact smoothGaugeForcing_eq_radial hh he hzero hf hfo hfzero hdfzero hr sigma
  rw [hlocal.deriv_eq]

end PoincareConjecture.M35.RadialGauge
