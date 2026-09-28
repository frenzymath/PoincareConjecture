import PoincareConjecture.Proofs.M47.BlowupControlsCapModelScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem cap_model_scalar_difference_sq_le_jet
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200)
    (B : RoundCylinderTwoTensor) (hclose : RoundCylinderClose epsilon 0 B)
    (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric 0 zero_lt_one))
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E2 q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U) :
    (D1.scalarCurvature (M35.cylinderCoordinateEquiv.symm (0, s)) - 1) ^ 2 ≤
      (16 / 5 : ℝ) ^ 2 * roundCylinderJetErrorSquared 0 B ⌊epsilon⁻¹⌋₊ (q, s) := by
  let g0 := M35.cylinderEuclideanMetric 0 zero_lt_one
  let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
    g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
  let x := M35.cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  let X := g0.tensorNorm H x
  let Y := g0.tensorNorm (D0.covariantTensorDerivative H) x
  let Z := g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative H)) x
  let J := roundCylinderJetErrorSquared 0 B ⌊epsilon⁻¹⌋₊ (q, s)
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    change (2 : ℝ) ≤ epsilon⁻¹
    rw [← one_div, le_div_iff₀ hepsilon]
    linarith only [hsmall]
  have henergy : X ^ 2 + Y ^ 2 + Z ^ 2 ≤ J :=
    cap_model_twoDerivative_energy_le_jet 0 zero_lt_one B g1 D0 q hU hcoeff s hx _ horder
  have hJ : 0 ≤ J := (by positivity : 0 ≤ X ^ 2 + Y ^ 2 + Z ^ 2).trans henergy
  have hsq : X ^ 2 + Y ^ 2 + Z ^ 2 ≤ (Real.sqrt J) ^ 2 := by
    rwa [Real.sq_sqrt hJ]
  have hlinear := cap_scalar_arithmetic_energy (Real.sqrt_nonneg J) hsq
  have hscalar := cap_model_scalar_difference_fine hepsilon hsmall (le_refl (0 : ℝ))
    B hclose g1 D1 D0 q hU hcoeff s hs hx
  have hscalar' : |D1.scalarCurvature x - 1| ≤
      (3 / 4 : ℝ) * X + (1 / 10 : ℝ) * Y + (31 / 10 : ℝ) * Z := by
    have hY : 0 ≤ Y := Real.sqrt_nonneg _
    norm_num only [sub_zero, div_one] at hscalar
    linarith only [hscalar, hY]
  have h := (sq_le_sq₀ (abs_nonneg _) (by positivity : (0 : ℝ) ≤ (16 / 5) * Real.sqrt J)).mpr
    (hscalar'.trans hlinear)
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hJ] using h

end PoincareConjecture.M47
