import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# A bilinear coefficient evaluated on a varying vector

The product rule separates the derivative of the coefficient from the
derivative of its input. This is used in the lowered Koszul calculation
on Morgan--Tian, pp. 3-7; M44 derivation 31.
-/

set_option autoImplicit false

namespace PoincareMT.M44

/-- The product rule for a bilinear form evaluated on a varying
bilinear map and one fixed vector. Source: the differentiated lowered
Koszul formula in M44 derivation 31. -/
theorem fderiv_bilinear_evaluation_bilinear
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : V → V →L[ℝ] V →L[ℝ] ℝ} {C : V → V →L[ℝ] V →L[ℝ] V} {x : V}
    (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C x)
    (d u v w : V) :
    fderiv ℝ (fun y => B y (C y u v) w) x d =
      fderiv ℝ B x d (C x u v) w + B x (fderiv ℝ C x d u v) w := by
  have he := (hB.hasFDerivAt.clm_apply
    ((hC.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
      (hasFDerivAt_const v x))).clm_apply (hasFDerivAt_const w x)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    add_apply, zero_apply, map_zero, add_zero, zero_add, add_comm] using
      congrArg (fun L => L d) he.fderiv

end PoincareMT.M44
