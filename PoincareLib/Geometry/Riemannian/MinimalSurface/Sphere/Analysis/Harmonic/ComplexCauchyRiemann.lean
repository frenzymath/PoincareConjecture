import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Complex differentiability from plane Cauchy-Riemann equations

The standard real orthonormal coordinates identify the plane used for
the Hopf coefficient with the complex plane. This is the elementary
complex-analysis step in Sacks-Uhlenbeck Lemma 1.5, printed p. 5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Topology

namespace PoincareMT.M60

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Real Cauchy-Riemann equations in standard plane coordinates imply
complex differentiability after the standard real-linear isometry.
Source: SU Lemma 1.5, p. 5, Hopf-differential calculation. -/
theorem differentiableAt_complex_of_plane_cauchyRiemann
    {a b : E → ℝ} {z : ℂ}
    (ha : DifferentiableAt ℝ a (Complex.orthonormalBasisOneI.repr z))
    (hb : DifferentiableAt ℝ b (Complex.orthonormalBasisOneI.repr z))
    (h1 : fderiv ℝ a (Complex.orthonormalBasisOneI.repr z)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      fderiv ℝ b (Complex.orthonormalBasisOneI.repr z)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1))
    (h2 : fderiv ℝ a (Complex.orthonormalBasisOneI.repr z)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      -fderiv ℝ b (Complex.orthonormalBasisOneI.repr z)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)) :
    DifferentiableAt ℂ (fun w => (a (Complex.orthonormalBasisOneI.repr w) : ℂ) +
      Complex.I * (b (Complex.orthonormalBasisOneI.repr w) : ℂ)) z := by
  let L := Complex.orthonormalBasisOneI.repr.toContinuousLinearMap
  have hL1 : L 1 = EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i
    fin_cases i <;> simp [L, Complex.orthonormalBasisOneI_repr_apply,
      EuclideanSpace.basisFun_apply]
  have hLI : L Complex.I = EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [L, Complex.orthonormalBasisOneI_repr_apply,
      EuclideanSpace.basisFun_apply]
  have hA := Complex.ofRealCLM.hasFDerivAt.comp z (ha.hasFDerivAt.comp z L.hasFDerivAt)
  have hB := Complex.ofRealCLM.hasFDerivAt.comp z (hb.hasFDerivAt.comp z L.hasFDerivAt)
  have hd := hA.add (hB.const_smul Complex.I)
  dsimp only [Function.comp_def, Complex.ofRealCLM_apply, smul_eq_mul] at hd
  change HasFDerivAt (fun w => (a (Complex.orthonormalBasisOneI.repr w) : ℂ) +
    Complex.I * (b (Complex.orthonormalBasisOneI.repr w) : ℂ)) _ z at hd
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_apply, smul_eq_mul, hL1, hLI, h1, h2, Complex.ofReal_neg]
  rw [mul_add, ← mul_assoc, Complex.I_mul_I]
  ring

end PoincareMT.M60
