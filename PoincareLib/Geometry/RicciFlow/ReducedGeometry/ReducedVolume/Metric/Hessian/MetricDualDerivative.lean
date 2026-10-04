import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Differentiating the coordinate metric dual

The inverse metric applied to a scalar differential is continuously
differentiable. Differentiating its defining covector identity avoids
choosing a formula for the derivative of the inverse operator.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareMT.ReducedVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth invertible bilinear form sends the differential of a C2 scalar to a C1 field. -/
theorem metricDual_contDiffAt {B : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → ℝ} {y : E}
    (hB : ContDiffAt ℝ 1 B y) (hf : ContDiffAt ℝ 2 f y)
    (hi : (B y).IsInvertible) :
    ContDiffAt ℝ 1 (fun z ↦ (B z).inverse (fderiv ℝ f z)) y := by
  exact (hi.contDiffAt_map_inverse.comp y hB).clm_apply
    (hf.fderiv_right (by norm_num))

/-- The derivative of the metric dual satisfies the differentiated defining identity. -/
theorem metricDual_fderiv_identity
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → ℝ} {y : E}
    (hB : ContDiffAt ℝ 1 B y) (hf : ContDiffAt ℝ 2 f y)
    (hi : (B y).IsInvertible) (v w : E) :
    B y (fderiv ℝ (fun z ↦ (B z).inverse (fderiv ℝ f z)) y v) w +
        fderiv ℝ B y v ((B y).inverse (fderiv ℝ f y)) w =
      fderiv ℝ (fderiv ℝ f) y v w := by
  let a := fun z ↦ (B z).inverse (fderiv ℝ f z)
  have ha := (metricDual_contDiffAt hB hf hi).differentiableAt one_ne_zero
  have hinv : ∀ᶠ z in 𝓝 y, (B z).IsInvertible :=
    hB.continuousAt (ContinuousLinearEquiv.isOpen.mem_nhds hi)
  have heq : (fun z ↦ B z (a z)) =ᶠ[𝓝 y] fderiv ℝ f := by
    filter_upwards [hinv] with z hz
    exact hz.self_apply_inverse _
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_clm_apply (hB.differentiableAt one_ne_zero) ha] at hd
  exact congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ ↦ L v w) hd

end PoincareMT.ReducedVolume
