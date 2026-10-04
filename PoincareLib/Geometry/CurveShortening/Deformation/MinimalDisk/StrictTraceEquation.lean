import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.Gauge.Regularity
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.ComplexGradient

/-!
# The actual matrix equation under the boundary coordinate and frame

The genuine real chain and product rules preserve the equation without
dividing by the disk differential. Source: M65 derivation 43, matrix
equation and isolated zeros, for Heinz 1970, pp. 99--105, and
MT 19.2, pp. 438--439.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Complex
open scoped Topology ContDiff

namespace PoincareMT.M65StrictTrace

open M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The genuine dbar chain rule under an actual holomorphic parameter.
Source: derivation 43, exact holomorphic pullback factors. -/
theorem dbar_comp_holomorphic {F : ℂ → E} {psi : ℂ → ℂ} {z p : ℂ}
    (hF : DifferentiableAt ℝ F (psi z)) (hpsi : HasDerivAt psi p z) :
    dbar (F ∘ psi) z = star p • dbar F (psi z) := by
  have hd := hF.hasFDerivAt.comp z (hpsi.hasFDerivAt.restrictScalars ℝ)
  have hcol (v : ℂ) : fderiv ℝ (F ∘ psi) z v = fderiv ℝ F (psi z) (v * p) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      congrArg (fun D : ℂ →L[ℝ] E => D v) hd.fderiv
  change (2 : ℂ)⁻¹ • (fderiv ℝ (F ∘ psi) z 1 +
    I • fderiv ℝ (F ∘ psi) z I) = star p •
      ((2 : ℂ)⁻¹ • (fderiv ℝ F (psi z) 1 + I • fderiv ℝ F (psi z) I))
  rw [hcol, hcol, one_mul]
  have hstar : star p = (p.re : ℂ) - (p.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have hlin : fderiv ℝ F (psi z) p + I • fderiv ℝ F (psi z) (I * p) =
      star p • (fderiv ℝ F (psi z) 1 + I • fderiv ℝ F (psi z) I) := by
    rw [hstar, realLinear_apply_complex _ p, realLinear_apply_complex _ (I * p)]
    simp only [I_mul_re, I_mul_im, ofReal_neg, smul_add, smul_smul,
      sub_mul, mul_assoc, I_mul_I, mul_neg_one, sub_neg_eq_add]
    module
  rw [hlin, smul_comm]

/-- The actual complex gradient gains the holomorphic derivative,
with its literal sign. Source: derivation 43, exact pullback factors. -/
theorem complexGradient_comp_holomorphic {n : ℕ}
    {G : ℂ → EuclideanSpace ℝ (Fin n)} {psi : ℂ → ℂ} {z p : ℂ}
    (hG : DifferentiableAt ℝ G (psi z)) (hpsi : HasDerivAt psi p z) :
    complexGradient (G ∘ psi) z = p • complexGradient G (psi z) := by
  have hd := hG.hasFDerivAt.comp z (hpsi.hasFDerivAt.restrictScalars ℝ)
  have hcol (v : ℂ) : fderiv ℝ (G ∘ psi) z v = fderiv ℝ G (psi z) (v * p) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      congrArg (fun D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin n) => D v) hd.fderiv
  let L := coordinateComplexification.comp (fderiv ℝ G (psi z))
  have hlin : L p - I • L (I * p) = p • (L 1 - I • L I) := by
    rw [realLinear_apply_complex L p, realLinear_apply_complex L (I * p)]
    conv_rhs => rw [← Complex.re_add_im p]
    simp only [I_mul_re, I_mul_im, ofReal_neg, smul_sub, smul_add, smul_smul,
      add_mul, mul_assoc, I_mul_I, mul_neg_one]
    module
  simpa only [complexGradient, hcol, one_mul, L, ContinuousLinearMap.comp_apply] using hlin

/-- The actual dbar product rule for a scalar and vector field.
Source: derivation 43, genuine matrix equation transport. -/
theorem dbar_smul {p : ℂ → ℂ} {F : ℂ → E} {z : ℂ}
    (hp : DifferentiableAt ℝ p z) (hF : DifferentiableAt ℝ F z) :
    dbar (fun w => p w • F w) z = dbar p z • F z + p z • dbar F z := by
  have hd := hp.hasFDerivAt.smul hF.hasFDerivAt
  have hcol (v : ℂ) : fderiv ℝ (fun w => p w • F w) z v =
      p z • fderiv ℝ F z v + fderiv ℝ p z v • F z := by
    exact congrArg (fun D : ℂ →L[ℝ] E => D v) hd.fderiv
  simp only [dbar, dbarLinear, smul_apply, add_apply, ContinuousLinearMap.apply_apply,
    hcol, smul_add, smul_smul, add_smul]
  module

/-- The actual pulled gradient satisfies the actual pulled matrix
equation. Source: derivation 43, exact holomorphic pullback factors. -/
theorem matrix_equation_holomorphic_pullback
    {F : ℂ → E} {A : ℂ → E →L[ℂ] E} {psi p : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F (psi z)) (hpsi : HasDerivAt psi (p z) z)
    (hp : DifferentiableAt ℂ p z) (heq : dbar F (psi z) = A (psi z) (F (psi z))) :
    dbar (fun w => p w • F (psi w)) z =
      (star (p z) • A (psi z)) (p z • F (psi z)) := by
  have hs : dbar (fun w => p w • F (psi w)) z =
      dbar p z • F (psi z) + p z • dbar (F ∘ psi) z := by
    convert! dbar_smul (hp.restrictScalars ℝ)
      (hF.comp z (hpsi.differentiableAt.restrictScalars ℝ)) using 1
  rw [hs, dbar_eq_zero_of_differentiableAt_complex hp, zero_smul, zero_add,
    dbar_comp_holomorphic hF hpsi, heq]
  simp only [smul_apply, map_smul, smul_smul]

/-- The actual invertible frame changes the matrix equation by the
genuine derivative product rule, in its literal multiplication order.
Source: derivation 43, actual frame coefficient. -/
theorem matrix_equation_under_frame
    {F : ℂ → E} {A L : ℂ → E →L[ℂ] E} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) (hL : DifferentiableAt ℝ L z)
    (hunit : IsUnit (L z)) (heq : dbar F z = A z (F z)) :
    dbar (fun w => L w (F w)) z =
      ((dbar L z + L z * A z) * Ring.inverse (L z)) (L z (F z)) := by
  rw [dbar_clm_apply hL hF, heq]
  have hinv : Ring.inverse (L z) (L z (F z)) = F z := by
    change (Ring.inverse (L z) * L z) (F z) = F z
    rw [Ring.inverse_mul_cancel _ hunit]
    rfl
  change _ = (dbar L z + L z * A z) (Ring.inverse (L z) (L z (F z)))
  rw [hinv]
  rfl

end PoincareMT.M65StrictTrace
