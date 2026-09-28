import PoincareConjecture.Proofs.M64.Mathlib.AffineEquivHessian
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ChartConnection
import PoincareConjecture.Definitions.M64Annulus






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Complex
open scoped ContDiff Topology

namespace PoincareConjecture.M64

open CoordinateExponential ConnectionVariation M65Branch

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)





theorem modulus_harmonic_equation_comp_affine
    {g : RiemannianMetric n E} (D : LeviCivitaData g)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {u : LoopPlane → E}
    {r : ℝ} (hr : 0 < r) (e : ℂ ≃L[ℝ] LoopPlane) (a : LoopPlane) (z : ℂ)
    (he1 : e 1 = r • EuclideanSpace.basisFun (Fin 2) ℝ 0)
    (heI : e I = EuclideanSpace.basisFun (Fin 2) ℝ 1 ∨
      e I = -EuclideanSpace.basisFun (Fin 2) ℝ 1)
    (hu : ContDiffAt ℝ ∞ u (a + e z))
    (hB : g.euclideanCoefficients =ᶠ[𝓝 (u (a + e z))] B)
    (heq :
      r • covDerivAlong (christoffelBilinear B) u
        (fun q => fderiv ℝ u q (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) (a + e z) +
      r⁻¹ • covDerivAlong (christoffelBilinear B) u
        (fun q => fderiv ℝ u q (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) (a + e z) = 0) :
    let H := fun w => u (a + e w)
    dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z) := by
  let H := fun w => u (a + e w)
  let p := a + e z
  let b0 := EuclideanSpace.basisFun (Fin 2) ℝ 0
  let b1 := EuclideanSpace.basisFun (Fin 2) ℝ 1
  have hP : HasFDerivAt (fun w => a + e w) e.toContinuousLinearMap z :=
    e.hasFDerivAt.const_add a
  have hH : ContDiffAt ℝ ∞ H z :=
    hu.comp z (contDiffAt_const.add e.contDiff.contDiffAt)
  have hcol (v : ℂ) : fderiv ℝ H z v = fderiv ℝ u p (e v) :=
    congrArg (fun L : ℂ →L[ℝ] E => L v)
      ((hu.differentiableAt (by simp)).hasFDerivAt.comp z hP).fderiv
  have hdd (v : LoopPlane) :
      fderiv ℝ (fun q => fderiv ℝ u q v) (a + e z) v =
        fderiv ℝ (fderiv ℝ u) (a + e z) v v := by
    rw [fderiv_clm_apply ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)) (differentiableAt_const v)]
    simp
  have hGamma := connectionCoefficient_eq_of_metric_germ D hB
  have hv :
      fderiv ℝ (fderiv ℝ H) z I I = fderiv ℝ (fderiv ℝ u) p b1 b1 := by
    rw [fderiv2_comp_affine_equiv]
    rcases heI with hi | hi <;> simp only [hi, map_neg, neg_apply, neg_neg, p, b1]
  have hvGamma :
      M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z I) (fderiv ℝ H z I) =
        christoffelBilinear B (u p) (fderiv ℝ u p b1) (fderiv ℝ u p b1) := by
    rw [hcol, hGamma]
    rcases heI with hi | hi <;> simp only [hi, map_neg, neg_apply, neg_neg, p, b1]
  have hweighted :
      r • (fderiv ℝ (fderiv ℝ u) p b0 b0 +
        christoffelBilinear B (u p) (fderiv ℝ u p b0) (fderiv ℝ u p b0)) +
      r⁻¹ • (fderiv ℝ (fderiv ℝ u) p b1 b1 +
        christoffelBilinear B (u p) (fderiv ℝ u p b1) (fderiv ℝ u p b1)) = 0 := by
    simpa only [covDerivAlong_def, hdd, p, b0, b1] using heq
  apply dbar_complexGradient_of_harmonic D hH
  rw [hv, hvGamma, fderiv2_comp_affine_equiv, hcol, hGamma, he1]
  simp only [map_smul, smul_apply, smul_smul]
  have hh := congrArg (fun v : E => r • v) hweighted
  simp only [smul_zero, smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at hh
  convert! hh using 1
  module

end PoincareConjecture.M64
