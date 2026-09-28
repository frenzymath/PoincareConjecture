import PoincareConjecture.Proofs.M47.BlowupControlsCapInverseMetric
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderLeviCivita
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem cap_native_frameInverseGram (q : UnitTwoSphere) (s : ℝ) (i j : Fin 3) :
    M04.frameInverseGram (M35.cylinderEuclideanMetric 0 (by norm_num))
      (M35.cylinderCoordinateEquiv.symm (0, s)) (ContinuousLinearMap.id ℝ E₃) i j =
      (roundCylinderGram 0 (chartAt E₂ q) (chartAt E₂ q q, s))⁻¹ i j := by
  let g := M35.cylinderEuclideanMetric 0 (by norm_num)
  let x := M35.cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  let A := M04.frameGramOperator g x (ContinuousLinearMap.id ℝ E₃)
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hi : A.IsInvertible :=
    M04.frameGramOperator_isInvertible g x (ContinuousLinearEquiv.refl ℝ E₃)
  have hpair := cap_frameGram_inner g x (ContinuousLinearMap.id ℝ E₃)
    (A.inverse (b j)) (b i)
  change inner ℝ (A (A.inverse (b j))) (b i) = g.inner x (A.inverse (b j)) (b i) at hpair
  rw [hi.self_apply_inverse] at hpair
  have hmetric := M35.cylinderEuclideanMetric_inner_basis 0 (by norm_num) x (A.inverse (b j)) i
  dsimp only [x] at hmetric
  rw [M35.cylinderCoordinateEquiv.apply_symm_apply] at hmetric
  norm_num at hmetric
  change inner ℝ (b i) (A.inverse (b j)) = _
  rw [M34.roundCylinderGram_chart_center_inv (by norm_num : (0 : ℝ) ≠ 1)]
  have hcoord : inner ℝ (b i) (A.inverse (b j)) = (A.inverse (b j)) i := by
    simp [b, EuclideanSpace.inner_single_left]
  rw [hcoord]
  have hp : inner ℝ (b j) (b i) = (![2, 2, 1] i : ℝ) * (A.inverse (b j)) i :=
    hpair.trans (by simpa only [g, x, b, EuclideanSpace.basisFun_apply] using hmetric)
  fin_cases i <;> fin_cases j <;>
    norm_num [b, EuclideanSpace.inner_single_left, Matrix.diagonal] at hp ⊢ <;> linarith

theorem cap_native_tensorNorm_sq (q : UnitTwoSphere) (s : ℝ) {r : ℕ}
    (T : CovariantTensorEvaluation 3 E₃ r)
    (hT : ∃ A : MultilinearMap ℝ (fun _ : Fin r => E₃) ℝ,
      ∀ v, T (M35.cylinderCoordinateEquiv.symm (0, s)) v = A v) :
    ((M35.cylinderEuclideanMetric 0 (by norm_num)).tensorNorm T
      (M35.cylinderCoordinateEquiv.symm (0, s))) ^ 2 =
      roundCylinderTensorNormSquared 0 (chartAt E₂ q) (chartAt E₂ q q, s)
        (fun a => T (M35.cylinderCoordinateEquiv.symm (0, s))
          (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))) := by
  have h := M04.tensorNorm_sq_eq_inverseGram
    (M35.cylinderEuclideanMetric 0 (by norm_num)) T
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
      (∏ j, M04.frameInverseGram (M35.cylinderEuclideanMetric 0 (by norm_num))
        (M35.cylinderCoordinateEquiv.symm (0, s)) (ContinuousLinearMap.id ℝ E₃) (a j) (b j)) = _
  simp only [cap_native_frameInverseGram q s]
  ring

theorem cap_native_tensorNorm (q : UnitTwoSphere) (s : ℝ) {r : ℕ}
    (T : CovariantTensorEvaluation 3 E₃ r)
    (hT : ∃ A : MultilinearMap ℝ (fun _ : Fin r => E₃) ℝ,
      ∀ v, T (M35.cylinderCoordinateEquiv.symm (0, s)) v = A v) :
    (M35.cylinderEuclideanMetric 0 (by norm_num)).tensorNorm T
      (M35.cylinderCoordinateEquiv.symm (0, s)) =
      Real.sqrt (roundCylinderTensorNormSquared 0 (chartAt E₂ q) (chartAt E₂ q q, s)
        (fun a => T (M35.cylinderCoordinateEquiv.symm (0, s))
          (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k)))) := by
  rw [← cap_native_tensorNorm_sq q s T hT]
  have hn : 0 ≤ (M35.cylinderEuclideanMetric 0 (by norm_num)).tensorNorm T
      (M35.cylinderCoordinateEquiv.symm (0, s)) := Real.sqrt_nonneg _
  rw [Real.sqrt_sq hn]

end PoincareConjecture.M47
