import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarCoefficientBound










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "V" => EuclideanSpace ℝ I
local notation "Idx" => Fin 4 → I



theorem cap_scalar_difference_tensor_bound
    {g0 g1 : RiemannianMetric 3 V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (e : V ≃L[ℝ] V) (x : V)
    (he : ∀ v w, g0.inner x (e v) (e w) = inner ℝ v w)
    (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0) :
    let b := EuclideanSpace.basisFun I ℝ
    let H : CovariantTensorEvaluation 3 V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    let X := g0.tensorNorm H x
    let Y := g0.tensorNorm (D0.covariantTensorDerivative H) x
    let Z := g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative H)) x
    let a := ‖(M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse‖
    let r := ‖(WithLp.toLp 2 (fun p : I × I => D0.ricci x (e (b p.1)) (e (b p.2))) :
      EuclideanSpace ℝ (I × I))‖
    |D1.scalarCurvature x - D0.scalarCurvature x| ≤ a * X * r +
      (3 + 2 * a * X * (Real.sqrt 3 * a + Real.sqrt 3)) * Z + 18 * a ^ 3 * Y ^ 2 := by
  let b := EuclideanSpace.basisFun I ℝ
  let H : CovariantTensorEvaluation 3 V 2 :=
    fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
  let T := D0.covariantTensorDerivative H
  let W := D0.covariantTensorDerivative T
  let X := g0.tensorNorm H x
  let Y := g0.tensorNorm T x
  let Z := g0.tensorNorm W x
  let Ai := (M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse
  let a := ‖Ai‖
  let A0 := M04.frameInverseGram g0 x e.toContinuousLinearMap
  let A := M04.frameInverseGram g1 x e.toContinuousLinearMap
  let r := ‖(WithLp.toLp 2 (fun p : I × I => D0.ricci x (e (b p.1)) (e (b p.2))) :
    EuclideanSpace ℝ (I × I))‖
  let P := fun i j k => T x ![e (b i), e (b j), e (b k)]
  let K := fun i j k l => W x ![e (b i), e (b j), e (b k), e (b l)]
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth g0 g1
  have hT : IsSmoothCovariantTensor T := M04.isSmoothCovariantTensor_covariantTensorDerivative D0 hH
  have hW : IsSmoothCovariantTensor W := M04.isSmoothCovariantTensor_covariantTensorDerivative D0 hT
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hPnorm : ‖capThreeTensorComponents P‖ = Y :=
    cap_tensorNorm_frame_triple g0 T x (hT.1 x) e he
  have hKnorm : ‖(WithLp.toLp 2 (fun v : Idx => K (v 0) (v 1) (v 2) (v 3)) :
      EuclideanSpace ℝ Idx)‖ = Z := by
    have hv : (fun v : Idx => K (v 0) (v 1) (v 2) (v 3)) =
        fun v : Idx => W x (fun j => e (b (v j))) := by
      funext v
      apply congrArg (W x)
      funext j
      fin_cases j <;> rfl
    rw [hv]
    exact cap_tensorNorm_frame g0 W x (hW.1 x) e he
  have herror : ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2 - A0 p.1 p.2) :
      EuclideanSpace ℝ (I × I))‖ ≤ a * X := by
    rw [cap_inverseError_components g0 g1 x e he]
    exact cap_inverseError_tensor_norm_le g0 g1 x e he
  have hc : capOperatorComponents (Ai - ContinuousLinearMap.id ℝ V) =
      capOperatorComponents Ai - capOperatorComponents (ContinuousLinearMap.id ℝ V) := by
    ext p
    simp only [capOperatorComponents, WithLp.ofLp_toLp, sub_apply,
      inner_sub_right, PiLp.sub_apply]
  have hdiff : ‖capOperatorComponents Ai - capOperatorComponents (ContinuousLinearMap.id ℝ V)‖ ≤
      a * X := by
    rw [← hc]
    exact cap_inverseError_tensor_norm_le g0 g1 x e he
  have hAi : ‖capOperatorComponents Ai‖ ≤ Real.sqrt 3 * a := cap_operatorComponents_norm_le Ai
  have hHessian : ‖capScalarHessianComponents (WithLp.toLp 2 (fun p : I × I => A p.1 p.2))‖ ≤
      3 + 2 * a * X * (Real.sqrt 3 * a + Real.sqrt 3) := by
    have hb := cap_scalarHessianComponents_norm_le (capOperatorComponents Ai)
    change ‖capScalarHessianComponents (capOperatorComponents Ai)‖ ≤ _
    refine hb.trans ?_
    calc
      _ ≤ 3 + (2 * (a * X)) * (Real.sqrt 3 * a + Real.sqrt 3) :=
        add_le_add le_rfl (mul_le_mul
          (mul_le_mul_of_nonneg_left hdiff (by norm_num)) (add_le_add hAi le_rfl)
          (by positivity) (by positivity))
      _ = _ := by ring
  have h := cap_scalar_difference_coefficient_bound D0 D1 e x hzero
  change |D1.scalarCurvature x - D0.scalarCurvature x| ≤
    ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2 - A0 p.1 p.2) :
      EuclideanSpace ℝ (I × I))‖ * r +
    ‖capScalarHessianComponents (WithLp.toLp 2 (fun p : I × I => A p.1 p.2))‖ *
      ‖(WithLp.toLp 2 (fun v : Idx => K (v 0) (v 1) (v 2) (v 3)) :
        EuclideanSpace ℝ Idx)‖ + 18 * a ^ 3 * ‖capThreeTensorComponents P‖ ^ 2 at h
  rw [hKnorm, hPnorm] at h
  refine h.trans ?_
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right herror (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hHessian hZ)) le_rfl

end PoincareConjecture.M47
