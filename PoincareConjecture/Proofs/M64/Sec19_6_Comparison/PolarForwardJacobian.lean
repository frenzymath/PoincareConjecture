import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarForwardMap
import Mathlib.MeasureTheory.Function.Jacobian










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Real

namespace PoincareConjecture

open Proofs.M58




theorem m64PolarForwardMap_det (p : LoopPlane) :
    (fderiv ℝ m64PolarForwardMap p).det = -(p 1 + 1) / 4 := by
  let L := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).smulRight
      (((1 / 2 : ℝ) * (p 1 + 1)) • angularVector (p 0)) +
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).smulRight
      ((1 / 2 : ℝ) • angularPoint (p 0))
  have h0 : L (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      ((1 / 2 : ℝ) * (p 1 + 1)) • angularVector (p 0) := by
    change (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0 •
        (((1 / 2 : ℝ) * (p 1 + 1)) • angularVector (p 0)) +
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) 1 •
        ((1 / 2 : ℝ) • angularPoint (p 0)) = _
    simp [EuclideanSpace.basisFun_apply]
  have h1 : L (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      (1 / 2 : ℝ) • angularPoint (p 0) := by
    change (EuclideanSpace.basisFun (Fin 2) ℝ 1) 0 •
        (((1 / 2 : ℝ) * (p 1 + 1)) • angularVector (p 0)) +
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) 1 •
        ((1 / 2 : ℝ) • angularPoint (p 0)) = _
    simp [EuclideanSpace.basisFun_apply]
  rw [(m64PolarForwardMap_hasFDerivAt p).fderiv]
  unfold ContinuousLinearMap.det
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr]
  change (L (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 0 *
      (L (EuclideanSpace.basisFun (Fin 2) ℝ 1)) 1 -
    (L (EuclideanSpace.basisFun (Fin 2) ℝ 1)) 0 *
      (L (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 1 = _
  rw [h0, h1]
  change (((1 / 2 : ℝ) * (p 1 + 1)) * -sin (p 0)) * ((1 / 2 : ℝ) * sin (p 0)) -
      ((1 / 2 : ℝ) * cos (p 0)) * (((1 / 2 : ℝ) * (p 1 + 1)) * cos (p 0)) =
    -(p 1 + 1) / 4
  calc
    _ = (-(p 1 + 1) / 4) * (sin (p 0) ^ 2 + cos (p 0) ^ 2) := by ring
    _ = _ := by rw [sin_sq_add_cos_sq, mul_one]




theorem m64PolarForwardMap_abs_det {p : LoopPlane} (hp : -1 < p 1) :
    |(fderiv ℝ m64PolarForwardMap p).det| = (p 1 + 1) / 4 := by
  rw [m64PolarForwardMap_det, neg_div, abs_neg, abs_of_pos]
  exact div_pos (by linarith) (by norm_num)

end PoincareConjecture
