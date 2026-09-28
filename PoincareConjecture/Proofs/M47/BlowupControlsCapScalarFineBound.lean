import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarArithmetic
import PoincareConjecture.Proofs.M04.ShiNormalCoordinates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "V" => EuclideanSpace ℝ I



theorem cap_scalar_difference_fine
    {g0 g1 : RiemannianMetric 3 V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (x : V) (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0)
    (hRic : g0.tensorNorm D0.ricciEvaluation x ≤ (71 / 100 : ℝ))
    (hX : g0.tensorNorm (fun y (v : Fin 2 → V) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) x ≤ (1 / 1200 : ℝ))
    (hY : g0.tensorNorm (D0.covariantTensorDerivative (fun y (v : Fin 2 → V) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1))) x ≤ (1 / 1200 : ℝ)) :
    let H : CovariantTensorEvaluation 3 V 2 :=
      fun y v => g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
    |D1.scalarCurvature x - D0.scalarCurvature x| ≤
      (3 / 4 : ℝ) * g0.tensorNorm H x +
        (1 / 50 : ℝ) * g0.tensorNorm (D0.covariantTensorDerivative H) x +
        (31 / 10 : ℝ) * g0.tensorNorm
          (D0.covariantTensorDerivative (D0.covariantTensorDerivative H)) x := by
  let H : CovariantTensorEvaluation 3 V 2 :=
    fun y v => g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
  obtain ⟨e, _sigma, _hb, he⟩ := M04.exists_shi_metric_frame g0 x
  let a := ‖(M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse‖
  let b := EuclideanSpace.basisFun I ℝ
  let r := ‖(WithLp.toLp 2 (fun p : I × I => D0.ricci x (e (b p.1)) (e (b p.2))) :
    EuclideanSpace ℝ (I × I))‖
  have hr : r ≤ (71 / 100 : ℝ) := by
    have hn := cap_tensorNorm_frame_pair g0 D0.ricciEvaluation x
      ((M04.isSmoothCovariantTensor_ricciEvaluation D0).1 x) e he
    exact hn.le.trans hRic
  have ha : a ≤ (1200 / 1199 : ℝ) := by
    have h := cap_metricDifference_inverse_norm_le g0 g1 x e he
      (by norm_num : (1 / 1200 : ℝ) < 1) hX
    norm_num only [sub_eq_add_neg, inv_div, neg_div, Nat.cast_ofNat] at h
    convert! h using 1
  have h := cap_scalar_difference_tensor_bound D0 D1 e x he hzero
  exact h.trans (cap_scalar_arithmetic_fine (norm_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg _) ha hX hY hr)

end PoincareConjecture.M47
