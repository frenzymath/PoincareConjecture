import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Complex.CauchyRiemann.Gauge
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The complex gradient and the real Laplacian

In the local branch-isolation proof of Sacks-Uhlenbeck Theorem 1.6,
printed p. 5, the complex gradient of a harmonic map satisfies a
first-order covariant Cauchy-Riemann equation. This file gives the
actual second-derivative identity for any real-linear complexification.
-/

set_option autoImplicit false

open Complex
open scoped Topology ContDiff

namespace PoincareMT.M60

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The complex gradient after a specified real-linear map into a
complex space. Source: SU Theorem 1.6, p. 5, local-frame derivation. -/
noncomputable def complexGradient (C : E →L[ℝ] V) (u : ℂ → E) (z : ℂ) : V :=
  C (fderiv ℝ u z 1) - I • C (fderiv ℝ u z I)

/-- A C2 map has a C1 complex gradient in the actual coordinate domain.
Source: SU Theorem 1.6, p. 5, local branch-isolation derivation. -/
theorem contDiffAt_complexGradient (C : E →L[ℝ] V) {u : ℂ → E} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) : ContDiffAt ℝ 1 (complexGradient C u) z := by
  have hd := hu.fderiv_right (m := 1) (by norm_num)
  exact (C.contDiff.contDiffAt.comp z (hd.clm_apply contDiffAt_const)).sub
    ((C.contDiff.contDiffAt.comp z (hd.clm_apply contDiffAt_const)).const_smul I)

/-- The actual antiholomorphic derivative of the complex gradient is
half the actual real Laplacian. Equality of mixed second derivatives
is justified by C2 regularity. Source: SU Theorem 1.6, p. 5. -/
theorem cauchyRiemannDerivative_complexGradient
    (C : E →L[ℝ] V) {u : ℂ → E} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    cauchyRiemannDerivative (complexGradient C u) z =
      (1 / 2 : ℝ) • C (fderiv ℝ (fderiv ℝ u) z 1 1 +
        fderiv ℝ (fderiv ℝ u) z I I) := by
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hcol (d : ℂ) : HasFDerivAt (fun w => C (fderiv ℝ u w d))
      (C.comp ((fderiv ℝ (fderiv ℝ u) z).flip d)) z := by
    have h := C.hasFDerivAt.comp z
      (hd.hasFDerivAt.clm_apply (hasFDerivAt_const d z))
    simpa only [Function.comp_def, fderiv_const, ContinuousLinearMap.comp_zero,
      zero_add] using h
  have hW := (hcol 1).sub ((hcol I).const_smul I)
  change HasFDerivAt (complexGradient C u) _ z at hW
  have hsym := (hu.isSymmSndFDerivAt (by norm_num)).eq 1 I
  unfold cauchyRiemannDerivative
  rw [hW.fderiv]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, map_add, smul_sub, smul_smul, I_mul_I,
    neg_one_smul, sub_neg_eq_add, hsym]
  congr 1
  abel

end PoincareMT.M60
