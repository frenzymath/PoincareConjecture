import PoincareConjecture.Proofs.M47.BlowupControlsCapNativeJets
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderContractions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem cap_model_frameInverseGram (u : ℝ) (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) (i j : Fin 3) :
    M04.frameInverseGram (M35.cylinderEuclideanMetric u hu)
      (M35.cylinderCoordinateEquiv.symm (0, s)) (ContinuousLinearMap.id ℝ E₃) i j =
      (roundCylinderGram u (chartAt E₂ q) (chartAt E₂ q q, s))⁻¹ i j := by
  let g := M35.cylinderEuclideanMetric u hu
  let x := M35.cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  let A := M04.frameGramOperator g x (ContinuousLinearMap.id ℝ E₃)
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hi : A.IsInvertible :=
    M04.frameGramOperator_isInvertible g x (ContinuousLinearEquiv.refl ℝ E₃)
  have hpair := cap_frameGram_inner g x (ContinuousLinearMap.id ℝ E₃)
    (A.inverse (b j)) (b i)
  change inner ℝ (A (A.inverse (b j))) (b i) = g.inner x (A.inverse (b j)) (b i) at hpair
  rw [hi.self_apply_inverse] at hpair
  have hmetric := M35.cylinderEuclideanMetric_inner_basis u hu x (A.inverse (b j)) i
  dsimp only [x] at hmetric
  rw [M35.cylinderCoordinateEquiv.apply_symm_apply] at hmetric
  have hdiag : (32 : ℝ) * (1 - u) / (‖(0 : E₂)‖ ^ 2 + 4) ^ 2 = 2 * (1 - u) := by
    norm_num
    ring
  rw [hdiag] at hmetric
  change inner ℝ (b i) (A.inverse (b j)) = _
  rw [M35.roundCylinderGram_inv_center hu]
  have hp : inner ℝ (b j) (b i) =
      (![2 * (1 - u), 2 * (1 - u), 1] i : ℝ) * (A.inverse (b j)) i :=
    hpair.trans (by simpa only [g, x, b, EuclideanSpace.basisFun_apply] using hmetric)
  have hd : (![2 * (1 - u), 2 * (1 - u), 1] i : ℝ) ≠ 0 := by
    fin_cases i <;> norm_num <;> linarith
  have hc : (A.inverse (b j)) i =
      inner ℝ (b j) (b i) / (![2 * (1 - u), 2 * (1 - u), 1] i : ℝ) :=
    (eq_div_iff hd).mpr (by nlinarith only [hp])
  rw [EuclideanSpace.basisFun_inner, hc]
  fin_cases i <;> fin_cases j <;>
    simp [b, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, Matrix.diagonal]

theorem cap_model_tensorNorm_sq (u : ℝ) (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ} (T : CovariantTensorEvaluation 3 E₃ r)
    (hT : ∃ A : MultilinearMap ℝ (fun _ : Fin r => E₃) ℝ,
      ∀ v, T (M35.cylinderCoordinateEquiv.symm (0, s)) v = A v) :
    ((M35.cylinderEuclideanMetric u hu).tensorNorm T
      (M35.cylinderCoordinateEquiv.symm (0, s))) ^ 2 =
      roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, s)
        (fun a => T (M35.cylinderCoordinateEquiv.symm (0, s))
          (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))) := by
  have h := M04.tensorNorm_sq_eq_inverseGram (M35.cylinderEuclideanMetric u hu) T
    (M35.cylinderCoordinateEquiv.symm (0, s)) hT (ContinuousLinearEquiv.refl ℝ E₃)
  dsimp only at h
  rw [h]
  unfold roundCylinderTensorNormSquared
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change T _ (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j)) *
    T _ (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (b j)) *
      (∏ j, M04.frameInverseGram (M35.cylinderEuclideanMetric u hu)
        (M35.cylinderCoordinateEquiv.symm (0, s)) (ContinuousLinearMap.id ℝ E₃) (a j) (b j)) = _
  simp only [cap_model_frameInverseGram u hu q s]
  ring

theorem cap_model_metricDifference_norm_sq
    (u : ℝ) (hu : u < 1) (g1 : RiemannianMetric 3 E₃)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u hu))
    (q : UnitTwoSphere) (B : RoundCylinderTwoTensor) {U : Set E₃} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E₂ q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U) (k : ℕ) :
    let H : CovariantTensorEvaluation 3 E₃ 2 := fun y v =>
      g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric u hu).inner y (v 0) (v 1)
    ((M35.cylinderEuclideanMetric u hu).tensorNorm
      (D0.iteratedCovariantTensorDerivative H k)
      (M35.cylinderCoordinateEquiv.symm (0, s))) ^ 2 =
      roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, s)
        (roundCylinderIteratedDerivative u (chartAt E₂ q) B k (chartAt E₂ q q, s)) := by
  dsimp only
  let H : CovariantTensorEvaluation 3 E₃ 2 := fun y v =>
    g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric u hu).inner y (v 0) (v 1)
  have hT := cap_iteratedCovariantTensorDerivative_smooth D0 H
    (cap_metricDifference_smooth _ _) k
  rw [cap_model_tensorNorm_sq u hu q s _ (hT.1 _)]
  congr 1
  funext a
  have h := cap_native_iterated_metricDifference u hu g1 D0 q B hU hcoeff k hx a
  simpa only [ContinuousLinearEquiv.apply_symm_apply, M35.sphere_chart_center] using h

end PoincareConjecture.M47
