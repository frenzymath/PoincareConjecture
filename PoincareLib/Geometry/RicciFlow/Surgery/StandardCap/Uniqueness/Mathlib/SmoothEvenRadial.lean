import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Mathlib.SmoothAxisDivision
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth Euclidean extension of even radial profiles

Morgan-Tian Section 12.6, pp. 307-314, and the corrected radial-gauge
tip requirement. A smooth even scalar profile on the signed axis gives
a genuinely smooth function of Euclidean radius, including the origin.
The derivative uses the actual integrated second derivative, so no
analyticity or assumed squared-radius factorization is needed.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped ContDiff Topology

namespace PoincareMT.M35.SmoothRadial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem hasFDerivAt_norm_explicit {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  convert! hn using 1
  · funext y
    simp only [Real.sqrt_sq_eq_abs, abs_norm]
  · ext v
    simp only [smul_apply, two_smul, add_apply, smul_eq_mul, Real.sqrt_sq_eq_abs, abs_norm]
    field_simp [norm_ne_zero_iff.mpr hx]
    ring

/-- At the tip the zero derivative of an even profile cancels the norm singularity. -/
theorem hasFDerivAt_even_norm_zero {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (he : Function.Even f) :
    HasFDerivAt (fun x : E => f ‖x‖) (0 : E →L[ℝ] ℝ) 0 := by
  have hd : HasDerivAt f 0 0 := by
    simpa only [deriv_zero_of_even hf he] using (hf 0).hasDerivAt
  have ho : (fun r : ℝ => f r - f 0) =o[𝓝 0] (fun r => r) := by
    simpa only [sub_zero, smul_zero] using hd.isLittleO
  have hn : Tendsto (fun x : E => ‖x‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm : Continuous (fun x : E => ‖x‖)).tendsto 0
  have hh : (fun x : E => f ‖x‖ - f 0) =o[𝓝 0] (fun x => ‖x‖) := ho.comp_tendsto hn
  have hh' : (fun x : E => f ‖x‖ - f 0) =o[𝓝 0] (fun x => x) := hh.of_norm_right
  rw [hasFDerivAt_iff_isLittleO]
  simpa only [norm_zero, zero_apply, sub_zero] using hh'

/-- The genuine radial derivative at every point, written without division by radius. -/
theorem hasFDerivAt_even_norm {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (x : E) :
    HasFDerivAt (fun y : E => f ‖y‖) (axisDivision (deriv f) ‖x‖ • innerSL ℝ x) x := by
  by_cases hx : x = 0
  · subst x
    simpa only [map_zero, smul_zero] using
      (hasFDerivAt_even_norm_zero (E := E) (hf.differentiable (by simp)) he)
  · have hd := (hf.differentiable (by simp) ‖x‖).hasDerivAt.comp_hasFDerivAt x
      (hasFDerivAt_norm_explicit hx)
    convert! hd using 1
    ext v
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_axisDivision_deriv hf he ‖x‖]
    field_simp [norm_ne_zero_iff.mpr hx]

/-- A smooth even profile extends smoothly to real Euclidean space in every dimension. -/
theorem contDiff_even_norm {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) : ContDiff ℝ ∞ (fun x : E => f ‖x‖) := by
  have hfinite : ∀ k : ℕ, ∀ f : ℝ → ℝ,
      ContDiff ℝ ∞ f → Function.Even f → ContDiff ℝ k (fun x : E => f ‖x‖) := by
    intro k
    induction k with
    | zero =>
      intro f hf _
      exact contDiff_zero.mpr (hf.continuous.comp continuous_norm)
    | succ k ih =>
      intro f hf he
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hasFDerivAt_even_norm hf he x).differentiableAt, by simp, ?_⟩
      have hq := ih (axisDivision (deriv f))
        (axisDivision_contDiff (contDiff_infty_iff_deriv.mp hf).2)
        (axisDivision_deriv_even hf he)
      have hd : fderiv ℝ (fun x : E => f ‖x‖) =
          fun x => axisDivision (deriv f) ‖x‖ • innerSL ℝ x :=
        funext (fun x => (hasFDerivAt_even_norm hf he x).fderiv)
      rw [hd]
      let B : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
      exact hq.smul B.contDiff
  exact contDiff_infty.mpr (fun k => hfinite k f hf he)

end PoincareMT.M35.SmoothRadial
