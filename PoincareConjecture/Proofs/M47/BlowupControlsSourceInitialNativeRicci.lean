import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialModelFrame
import PoincareConjecture.Proofs.M47.BlowupControlsCapModelEnergy
import PoincareConjecture.Proofs.M47.CanonicalNeckRicciDiagonals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem source_initial_native_axial_bounds
    {epsilon u : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 2)
    (hu : u < 1) (B : RoundCylinderTwoTensor)
    (hclose : RoundCylinderClose epsilon u B)
    (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u hu))
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E2 q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U) :
    let x := M35.cylinderCoordinateEquiv.symm (0, s)
    let v := EuclideanSpace.basisFun (Fin 3) ℝ 2
    |D1.ricci x v v| ≤ 54 * epsilon + 2430 * epsilon ^ 2 ∧
      1 / 2 ≤ g1.inner x v v := by
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    change (2 : ℝ) ≤ epsilon⁻¹
    rw [← one_div, le_div_iff₀ hepsilon]
    linarith only [hsmall]
  have hbound := cap_model_derivative_norm_le hepsilon hu B hclose g1 D0 q hU hcoeff s hs hx
  have hricci := Proofs.M47.neck_ricci_diagonal_error_bound D0 D1 _
    (sourceInitialModelFrame u hu) (sourceInitialModelFrame_isometry u hu s)
    (cap_model_connection_normal u hu D0 q s) hepsilon.le hsmall
    (hbound 0 (by omega)) (hbound 1 (by omega)) (hbound 2 horder) 2
  have hmodel := sourceInitialModelFrame_isometry u hu s
    (EuclideanSpace.basisFun (Fin 3) ℝ 2) (EuclideanSpace.basisFun (Fin 3) ℝ 2)
  rw [sourceInitialModelFrame_axial] at hmodel
  simp only [real_inner_self_eq_norm_sq, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one,
    one_pow] at hmodel
  have hmetric := cap_metricDifference_quadratic_le (M35.cylinderEuclideanMetric u hu) g1
    (M35.cylinderCoordinateEquiv.symm (0, s)) (EuclideanSpace.basisFun (Fin 3) ℝ 2)
  rw [hmodel, mul_one] at hmetric
  have herror := hmetric.trans (hbound 0 (by omega))
  rw [sourceInitialModelFrame_axial_ricci u hu D0 q s,
    sourceInitialModelFrame_axial, sub_zero] at hricci
  exact ⟨hricci, by linarith only [(abs_le.mp herror).1, hsmall]⟩

end PoincareConjecture.M47
