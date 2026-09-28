import PoincareConjecture.Proofs.M47.BlowupControlsCapModelEnergy
import PoincareConjecture.Proofs.M47.BlowupControlsCapModelRicciNorm
import PoincareConjecture.Proofs.M47.BlowupControlsCapModelNormal
import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarFineBound
import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarCoarseBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

private theorem two_le_accuracy_order {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ 1 / 2) : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
  apply Nat.le_floor
  change (2 : ℝ) ≤ epsilon⁻¹
  rw [← one_div, le_div_iff₀ hepsilon]
  linarith only [hsmall]

theorem cap_model_scalar_difference_fine
    {epsilon u : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200)
    (hu : u ≤ 0) (B : RoundCylinderTwoTensor)
    (hclose : RoundCylinderClose epsilon u B)
    (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u (by linarith)))
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E2 q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U) :
    let g0 := M35.cylinderEuclideanMetric u (by linarith)
    let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
    let x := M35.cylinderCoordinateEquiv.symm (0, s)
    |D1.scalarCurvature x - 1 / (1 - u)| ≤
      (3 / 4 : ℝ) * g0.tensorNorm H x +
        (1 / 50 : ℝ) * g0.tensorNorm (D0.covariantTensorDerivative H) x +
        (31 / 10 : ℝ) * g0.tensorNorm
          (D0.covariantTensorDerivative (D0.covariantTensorDerivative H)) x := by
  have horder := two_le_accuracy_order hepsilon (by linarith only [hsmall])
  have hbound := cap_model_derivative_norm_le hepsilon (by linarith : u < 1)
    B hclose g1 D0 q hU hcoeff s hs hx
  have h := cap_scalar_difference_fine D0 D1 _
    (cap_model_connection_normal u (by linarith) D0 q s)
    (cap_model_ricciNorm_le u hu D0 q s)
    ((hbound 0 (by omega)).trans hsmall) ((hbound 1 (by omega)).trans hsmall)
  simpa only [M35.cylinder_scalarCurvature_center u (by linarith) D0 q s] using h

theorem cap_model_scalar_difference_le
    {epsilon u : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (hu : u ≤ 0) (B : RoundCylinderTwoTensor)
    (hclose : RoundCylinderClose epsilon u B)
    (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u (by linarith)))
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E2 q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U) :
    |D1.scalarCurvature (M35.cylinderCoordinateEquiv.symm (0, s)) - 1 / (1 - u)| ≤
      (16 / 5 : ℝ) * epsilon := by
  have horder := two_le_accuracy_order hepsilon (by linarith only [hsmall])
  have hbound := cap_model_derivative_norm_le hepsilon (by linarith : u < 1)
    B hclose g1 D0 q hU hcoeff s hs hx
  have h := cap_scalar_difference_coarse D0 D1 _
    (cap_model_connection_normal u (by linarith) D0 q s)
    (cap_model_ricciNorm_le u hu D0 q s)
    ((hbound 0 (by omega)).trans hsmall) ((hbound 1 (by omega)).trans hsmall)
  have henergy := cap_model_twoDerivative_energy_le_jet u (by linarith) B g1 D0 q
    hU hcoeff s hx ⌊epsilon⁻¹⌋₊ horder
  obtain ⟨bound, hbound, hjet⟩ := hclose.2
  have htotal := henergy.trans ((hjet (q, s) hs).trans hbound.le)
  have hfinal := h.trans (cap_scalar_arithmetic_energy hepsilon.le htotal)
  simpa only [M35.cylinder_scalarCurvature_center u (by linarith) D0 q s] using hfinal

theorem cap_model_scalar_gt_quarter
    {epsilon u : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (hu : u ∈ Icc (-1) 0) (B : RoundCylinderTwoTensor)
    (hclose : RoundCylinderClose epsilon u B)
    (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u (by linarith [hu.2])))
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E2 q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U) :
    (1 / 4 : ℝ) < D1.scalarCurvature (M35.cylinderCoordinateEquiv.symm (0, s)) := by
  have h := cap_model_scalar_difference_le hepsilon hsmall hu.2 B hclose g1 D1 D0 q
    hU hcoeff s hs hx
  have hmodel : (1 / 2 : ℝ) ≤ 1 / (1 - u) := by
    rw [le_div_iff₀ (by linarith [hu.2] : 0 < 1 - u)]
    linarith [hu.1]
  have hlower := (abs_le.mp h).1
  linarith only [hlower, hsmall, hmodel]

end PoincareConjecture.M47
