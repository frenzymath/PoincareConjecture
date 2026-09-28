import PoincareConjecture.Proofs.M47.BlowupControlsCapThreeArrays
import PoincareConjecture.Proofs.M47.BlowupControlsCapConnectionCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "V" => EuclideanSpace ℝ I
local notation "Tensor" => I → I → I → ℝ

theorem cap_koszul_array_norm_le (P : Tensor) :
    ‖capThreeTensorComponents (fun k i j => P i j k + P j i k - P k i j)‖ ≤
      3 * ‖capThreeTensorComponents P‖ := by
  have heq : capThreeTensorComponents (fun k i j => P i j k + P j i k - P k i j) =
      capThreeTensorComponents (fun k i j => P i j k) +
        capThreeTensorComponents (fun k i j => P j i k) - capThreeTensorComponents P := by
    ext p
    rfl
  have hsecond : ‖capThreeTensorComponents (fun k i j => P j i k)‖ =
      ‖capThreeTensorComponents P‖ :=
    (cap_threeTensor_cyclic_norm (fun i j k => P j i k)).trans (cap_threeTensor_swap_norm P)
  rw [heq]
  calc
    _ ≤ ‖capThreeTensorComponents (fun k i j => P i j k) +
        capThreeTensorComponents (fun k i j => P j i k)‖ + ‖capThreeTensorComponents P‖ :=
      norm_sub_le _ _
    _ ≤ (‖capThreeTensorComponents (fun k i j => P i j k)‖ +
        ‖capThreeTensorComponents (fun k i j => P j i k)‖) + ‖capThreeTensorComponents P‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by rw [cap_threeTensor_cyclic_norm, hsecond]; ring

theorem cap_threeTensor_operator_action_norm_le (L : V →L[ℝ] V) (T : Tensor) :
    ‖capThreeTensorComponents (fun k i j =>
      L (WithLp.toLp 2 (fun l => T l i j)) k)‖ ≤ ‖L‖ * ‖capThreeTensorComponents T‖ := by
  have h := cap_array_operator_action_norm_le L
    (fun p : I × I => (WithLp.toLp 2 (fun l => T l p.1 p.2) : V))
  have hr (W : Tensor) :
      ‖(WithLp.toLp 2 (fun p : (I × I) × I => W p.2 p.1.1 p.1.2) :
        EuclideanSpace ℝ ((I × I) × I))‖ = ‖capThreeTensorComponents W‖ :=
    cap_array_norm_reindex (Equiv.prodComm (I × I) I) (fun p => W p.1 p.2.1 p.2.2)
  have hleft := hr (fun k i j => L (WithLp.toLp 2 (fun l => T l i j)) k)
  have hright := hr T
  change _ ≤ ‖L‖ * ‖(WithLp.toLp 2 (fun p : (I × I) × I => T p.2 p.1.1 p.1.2) :
    EuclideanSpace ℝ ((I × I) × I))‖ at h
  rw [hleft, hright] at h
  exact h

private theorem operator_apply_sum (L : V →L[ℝ] V) (v : V) (k : I) :
    L v k = ∑ l, inner ℝ (EuclideanSpace.basisFun I ℝ k)
      (L (EuclideanSpace.basisFun I ℝ l)) * v l := by
  let b := EuclideanSpace.basisFun I ℝ
  have h := congrArg (fun w : V => inner ℝ (b k) (L w)) (b.sum_repr v)
  simpa only [map_sum, map_smul, inner_sum, inner_smul_right, b,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_repr, mul_comm] using h.symm

theorem cap_connectionDifference_components_norm_le
    {g0 g1 : RiemannianMetric 3 V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (e : V ≃L[ℝ] V) (x : V) :
    let b := EuclideanSpace.basisFun I ℝ
    let H : CovariantTensorEvaluation 3 V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    let P := fun i j k => D0.covariantTensorDerivative H x ![e (b i), e (b j), e (b k)]
    let B := fun k i j => inner ℝ (b k) (e.symm
      (D1.euclideanConnection (e (b i)) (e (b j)) x -
        D0.euclideanConnection (e (b i)) (e (b j)) x))
    ‖capThreeTensorComponents B‖ ≤ (3 / 2 : ℝ) *
      ‖(M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse‖ *
        ‖capThreeTensorComponents P‖ := by
  let b := EuclideanSpace.basisFun I ℝ
  let H : CovariantTensorEvaluation 3 V 2 :=
    fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
  let P := fun i j k => D0.covariantTensorDerivative H x ![e (b i), e (b j), e (b k)]
  let S := fun k i j => P i j k + P j i k - P k i j
  let A := (M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse
  let B := fun k i j => inner ℝ (b k) (e.symm
    (D1.euclideanConnection (e (b i)) (e (b j)) x -
      D0.euclideanConnection (e (b i)) (e (b j)) x))
  have heq : capThreeTensorComponents B = (1 / 2 : ℝ) •
      capThreeTensorComponents (fun k i j => A (WithLp.toLp 2 (fun l => S l i j)) k) := by
    ext p
    change B p.1 p.2.1 p.2.2 = (1 / 2 : ℝ) * A (WithLp.toLp 2 (fun l => S l p.2.1 p.2.2)) p.1
    rw [operator_apply_sum]
    exact cap_connectionDifference_coefficients D0 D1 e x (e (b p.2.1)) (e (b p.2.2)) p.1
  change ‖capThreeTensorComponents B‖ ≤ (3 / 2 : ℝ) * ‖A‖ * ‖capThreeTensorComponents P‖
  rw [heq, norm_smul, Real.norm_eq_abs]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (‖A‖ * ‖capThreeTensorComponents S‖) :=
      mul_le_mul_of_nonneg_left (cap_threeTensor_operator_action_norm_le A S) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (‖A‖ * (3 * ‖capThreeTensorComponents P‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (cap_koszul_array_norm_le P) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

end PoincareConjecture.M47
