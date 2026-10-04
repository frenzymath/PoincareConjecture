import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Polar.ForwardMap
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Jacobian of the rectangle-to-collar coordinates

In the fixed Euclidean plane basis the angular and radial columns have
determinant minus one quarter of one plus the radial rectangle coordinate.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Real

namespace PoincareMT

open Proofs.M58

/-- The forward polar Jacobian determinant is minus one quarter times one plus the radial
coordinate. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar
in `proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
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

/-- Positive radius identifies the absolute polar Jacobian determinant. Source: Auxiliary
step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64PolarForwardMap_abs_det {p : LoopPlane} (hp : -1 < p 1) :
    |(fderiv ℝ m64PolarForwardMap p).det| = (p 1 + 1) / 4 := by
  rw [m64PolarForwardMap_det, neg_div, abs_neg, abs_of_pos]
  exact div_pos (by linarith) (by norm_num)

end PoincareMT
